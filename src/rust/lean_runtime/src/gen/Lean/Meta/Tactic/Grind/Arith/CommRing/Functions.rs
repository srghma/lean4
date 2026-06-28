// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
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
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value:
    crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value:
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
    m_data: [96, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value:
    crate::leanh::LeanStringObject<59> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value:
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
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value:
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
    m_data: [110, 112, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        18388652353510661091 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value:
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
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value:
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
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12847922472053947547 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14765357657372582228 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5779414593499529281 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9594062259507646949 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        5442360487226035463 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        10680564408669940870 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        10135981711945425184 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value:
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
    m_data: [82, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value:
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
    m_data: [116, 111, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        18169824201013588232 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value:
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
    m_data: [72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        16856108565602861689 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value:
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
    m_data: [104, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        16856108565602861689 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        4187025665268973031 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        18134279130838690737 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        7102027102192867304 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        1611444129324655608 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value:
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
    m_data: [116, 111, 78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        10040236838748678500 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        17185717442815859305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value:
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
    m_data: [99, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        439118677539554485 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14561037289535094017 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        4977321555018234431 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut crate::leanh::LeanObject,9341924117480681831 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value:
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
    m_data: [70, 105, 101, 108, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value:
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
    m_data: [116, 111, 73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        8615353994042975301 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        7723290638220826725 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value:
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
    m_data: [73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        1412621069384631438 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value:
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
    m_data: [105, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        1412621069384631438 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        10171450186735820607 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(
    mut v_msgData_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = lean_st_ref_get(v___y_1303_);
    v_env_1306_ = crate::leanh::lean_ctor_get(v___x_1305_, 0);
    crate::leanh::lean_inc_ref(v_env_1306_);
    crate::leanh::lean_dec(v___x_1305_);
    v___x_1307_ = lean_st_ref_get(v___y_1301_);
    v_mctx_1308_ = crate::leanh::lean_ctor_get(v___x_1307_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1308_);
    crate::leanh::lean_dec(v___x_1307_);
    v_lctx_1309_ = crate::leanh::lean_ctor_get(v___y_1300_, 2);
    v_options_1310_ = crate::leanh::lean_ctor_get(v___y_1302_, 2);
    crate::leanh::lean_inc_ref(v_options_1310_);
    crate::leanh::lean_inc_ref(v_lctx_1309_);
    v___x_1311_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1311_, 0, v_env_1306_);
    crate::leanh::lean_ctor_set(v___x_1311_, 1, v_mctx_1308_);
    crate::leanh::lean_ctor_set(v___x_1311_, 2, v_lctx_1309_);
    crate::leanh::lean_ctor_set(v___x_1311_, 3, v_options_1310_);
    v___x_1312_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1312_, 0, v___x_1311_);
    crate::leanh::lean_ctor_set(v___x_1312_, 1, v_msgData_1299_);
    v___x_1313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1313_, 0, v___x_1312_);
    return v___x_1313_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(
    mut v_msgData_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msgData_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
    crate::leanh::lean_dec(v___y_1318_);
    crate::leanh::lean_dec_ref(v___y_1317_);
    crate::leanh::lean_dec(v___y_1316_);
    crate::leanh::lean_dec_ref(v___y_1315_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(
    mut v_msg_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1327_ = crate::leanh::lean_ctor_get(v___y_1324_, 5);
                v___x_1328_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msg_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
                v_a_1329_ = crate::leanh::lean_ctor_get(v___x_1328_, 0);
                v_isSharedCheck_1337_ = (!crate::leanh::lean_is_exclusive(v___x_1328_)) as u8;
                if v_isSharedCheck_1337_ == 0 {
                    v___x_1331_ = v___x_1328_;
                    v_isShared_1332_ = v_isSharedCheck_1337_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1329_);
                    crate::leanh::lean_dec(v___x_1328_);
                    v___x_1331_ = crate::leanh::lean_box(0);
                    v_isShared_1332_ = v_isSharedCheck_1337_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1327_);
                v___x_1333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1333_, 0, v_ref_1327_);
                crate::leanh::lean_ctor_set(v___x_1333_, 1, v_a_1329_);
                if v_isShared_1332_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1331_, 1);
                    crate::leanh::lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
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
    mut v_msg_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(
            v_msg_1338_,
            v___y_1339_,
            v___y_1340_,
            v___y_1341_,
            v___y_1342_,
        );
    crate::leanh::lean_dec(v___y_1342_);
    crate::leanh::lean_dec_ref(v___y_1341_);
    crate::leanh::lean_dec(v___y_1340_);
    crate::leanh::lean_dec_ref(v___y_1339_);
    return v_res_1344_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0;
    v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
    return v___x_1347_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2;
    v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
    return v___x_1350_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4;
    v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
    return v___x_1353_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6;
    v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
    return v___x_1356_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkInst(
    mut v_declName_1357_: *mut crate::leanh::LeanObject,
    mut v_inst_1358_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_a_1362_: *mut crate::leanh::LeanObject,
    mut v_a_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_a_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_inst_x27_1359_);
                crate::leanh::lean_inc_ref(v_inst_1358_);
                v___x_1365_ = l_Lean_Meta_isDefEqI(
                    v_inst_1358_,
                    v_inst_x27_1359_,
                    v_a_1360_,
                    v_a_1361_,
                    v_a_1362_,
                    v_a_1363_,
                );
                if crate::leanh::lean_obj_tag(v___x_1365_) == 0 {
                    v_a_1366_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1389_ = (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1368_ = v___x_1365_;
                        v_isShared_1369_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1366_);
                        crate::leanh::lean_dec(v___x_1365_);
                        v___x_1368_ = crate::leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inst_x27_1359_);
                    crate::leanh::lean_dec_ref(v_inst_1358_);
                    crate::leanh::lean_dec(v_declName_1357_);
                    v_a_1390_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1397_ = (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1397_ == 0 {
                        v___x_1392_ = v___x_1365_;
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1390_);
                        crate::leanh::lean_dec(v___x_1365_);
                        v___x_1392_ = crate::leanh::lean_box(0);
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1370_ = (crate::leanh::lean_unbox(v_a_1366_) as u8);
                crate::leanh::lean_dec(v_a_1366_);
                if v___x_1370_ == 0 {
                    crate::leanh::lean_del_object(v___x_1368_);
                    v___x_1371_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1,
                    );
                    v___x_1372_ = l_Lean_MessageData_ofName(v_declName_1357_);
                    v___x_1373_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1373_, 0, v___x_1371_);
                    crate::leanh::lean_ctor_set(v___x_1373_, 1, v___x_1372_);
                    v___x_1374_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3,
                    );
                    v___x_1375_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1373_);
                    crate::leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
                    v___x_1376_ = l_Lean_indentExpr(v_inst_1358_);
                    v___x_1377_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1377_, 0, v___x_1375_);
                    crate::leanh::lean_ctor_set(v___x_1377_, 1, v___x_1376_);
                    v___x_1378_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5,
                    );
                    v___x_1379_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1379_, 0, v___x_1377_);
                    crate::leanh::lean_ctor_set(v___x_1379_, 1, v___x_1378_);
                    v___x_1380_ = l_Lean_indentExpr(v_inst_x27_1359_);
                    v___x_1381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1381_, 0, v___x_1379_);
                    crate::leanh::lean_ctor_set(v___x_1381_, 1, v___x_1380_);
                    v___x_1382_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7,
                    );
                    v___x_1383_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1383_, 0, v___x_1381_);
                    crate::leanh::lean_ctor_set(v___x_1383_, 1, v___x_1382_);
                    v___x_1384_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v___x_1383_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
                    return v___x_1384_;
                } else {
                    crate::leanh::lean_dec_ref(v_inst_x27_1359_);
                    crate::leanh::lean_dec_ref(v_inst_1358_);
                    crate::leanh::lean_dec(v_declName_1357_);
                    v___x_1385_ = crate::leanh::lean_box(0);
                    if v_isShared_1369_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1385_);
                        v___x_1387_ = v___x_1368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
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
                    v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
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
    mut v_declName_1398_: *mut crate::leanh::LeanObject,
    mut v_inst_1399_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
        v_declName_1398_,
        v_inst_1399_,
        v_inst_x27_1400_,
        v_a_1401_,
        v_a_1402_,
        v_a_1403_,
        v_a_1404_,
    );
    crate::leanh::lean_dec(v_a_1404_);
    crate::leanh::lean_dec_ref(v_a_1403_);
    crate::leanh::lean_dec(v_a_1402_);
    crate::leanh::lean_dec_ref(v_a_1401_);
    return v_res_1406_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(
    mut v_00_u03b1_1407_: *mut crate::leanh::LeanObject,
    mut v_msg_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1415_: *mut crate::leanh::LeanObject,
    mut v_msg_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
    mut v___y_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(
        v_00_u03b1_1415_,
        v_msg_1416_,
        v___y_1417_,
        v___y_1418_,
        v___y_1419_,
        v___y_1420_,
    );
    crate::leanh::lean_dec(v___y_1420_);
    crate::leanh::lean_dec_ref(v___y_1419_);
    crate::leanh::lean_dec(v___y_1418_);
    crate::leanh::lean_dec_ref(v___y_1417_);
    return v_res_1422_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(
    mut v_inst_1423_: *mut crate::leanh::LeanObject,
    mut v_declName_1424_: *mut crate::leanh::LeanObject,
    mut v___x_1425_: *mut crate::leanh::LeanObject,
    mut v_type_1426_: *mut crate::leanh::LeanObject,
    mut v_inst_1427_: *mut crate::leanh::LeanObject,
    mut v_____r_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1429_ = crate::leanh::lean_ctor_get(v_inst_1423_, 0);
    crate::leanh::lean_inc(v_canonExpr_1429_);
    crate::leanh::lean_dec_ref(v_inst_1423_);
    v___x_1430_ = l_Lean_mkConst(v_declName_1424_, v___x_1425_);
    v___x_1431_ = l_Lean_mkAppB(v___x_1430_, v_type_1426_, v_inst_1427_);
    v___x_1432_ = crate::leanh::lean_apply_1(v_canonExpr_1429_, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(
    mut v_inst_1433_: *mut crate::leanh::LeanObject,
    mut v_declName_1434_: *mut crate::leanh::LeanObject,
    mut v___x_1435_: *mut crate::leanh::LeanObject,
    mut v_type_1436_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1437_: *mut crate::leanh::LeanObject,
    mut v_inst_1438_: *mut crate::leanh::LeanObject,
    mut v_toBind_1439_: *mut crate::leanh::LeanObject,
    mut v_inst_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1440_);
    crate::leanh::lean_inc(v_declName_1434_);
    v___f_1441_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1441_, 0, v_inst_1433_);
    crate::leanh::lean_closure_set(v___f_1441_, 1, v_declName_1434_);
    crate::leanh::lean_closure_set(v___f_1441_, 2, v___x_1435_);
    crate::leanh::lean_closure_set(v___f_1441_, 3, v_type_1436_);
    crate::leanh::lean_closure_set(v___f_1441_, 4, v_inst_1440_);
    v___x_1442_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1442_, 0, v_declName_1434_);
    crate::leanh::lean_closure_set(v___x_1442_, 1, v_inst_1440_);
    crate::leanh::lean_closure_set(v___x_1442_, 2, v_expectedInst_1437_);
    v___x_1443_ = crate::leanh::lean_apply_2(v_inst_1438_, crate::leanh::lean_box(0), v___x_1442_);
    v___x_1444_ = crate::leanh::lean_apply_4(
        v_toBind_1439_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1443_,
        v___f_1441_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(
    mut v_inst_1445_: *mut crate::leanh::LeanObject,
    mut v_inst_1446_: *mut crate::leanh::LeanObject,
    mut v_inst_1447_: *mut crate::leanh::LeanObject,
    mut v_inst_1448_: *mut crate::leanh::LeanObject,
    mut v_type_1449_: *mut crate::leanh::LeanObject,
    mut v_u_1450_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1451_: *mut crate::leanh::LeanObject,
    mut v_declName_1452_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1454_ = crate::leanh::lean_ctor_get(v_inst_1447_, 1);
    crate::leanh::lean_inc_n(v_toBind_1454_, 2);
    v___x_1455_ = crate::leanh::lean_box(0);
    v___x_1456_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1456_, 0, v_u_1450_);
    crate::leanh::lean_ctor_set(v___x_1456_, 1, v___x_1455_);
    crate::leanh::lean_inc_ref(v_type_1449_);
    crate::leanh::lean_inc_ref(v___x_1456_);
    crate::leanh::lean_inc_ref(v_inst_1448_);
    v___f_1457_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1457_, 0, v_inst_1448_);
    crate::leanh::lean_closure_set(v___f_1457_, 1, v_declName_1452_);
    crate::leanh::lean_closure_set(v___f_1457_, 2, v___x_1456_);
    crate::leanh::lean_closure_set(v___f_1457_, 3, v_type_1449_);
    crate::leanh::lean_closure_set(v___f_1457_, 4, v_expectedInst_1453_);
    crate::leanh::lean_closure_set(v___f_1457_, 5, v_inst_1445_);
    crate::leanh::lean_closure_set(v___f_1457_, 6, v_toBind_1454_);
    v___x_1458_ = l_Lean_mkConst(v_instDeclName_1451_, v___x_1456_);
    v___x_1459_ = l_Lean_Expr_app___override(v___x_1458_, v_type_1449_);
    v___x_1460_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1447_,
        v_inst_1446_,
        v_inst_1448_,
        v___x_1459_,
    );
    v___x_1461_ = crate::leanh::lean_apply_4(
        v_toBind_1454_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1460_,
        v___f_1457_,
    );
    return v___x_1461_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(
    mut v_m_1462_: *mut crate::leanh::LeanObject,
    mut v_inst_1463_: *mut crate::leanh::LeanObject,
    mut v_inst_1464_: *mut crate::leanh::LeanObject,
    mut v_inst_1465_: *mut crate::leanh::LeanObject,
    mut v_inst_1466_: *mut crate::leanh::LeanObject,
    mut v_type_1467_: *mut crate::leanh::LeanObject,
    mut v_u_1468_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1469_: *mut crate::leanh::LeanObject,
    mut v_declName_1470_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1473_: *mut crate::leanh::LeanObject,
    mut v_declName_1474_: *mut crate::leanh::LeanObject,
    mut v___x_1475_: *mut crate::leanh::LeanObject,
    mut v_type_1476_: *mut crate::leanh::LeanObject,
    mut v_inst_1477_: *mut crate::leanh::LeanObject,
    mut v_____r_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1479_ = crate::leanh::lean_ctor_get(v_inst_1473_, 0);
    crate::leanh::lean_inc(v_canonExpr_1479_);
    crate::leanh::lean_dec_ref(v_inst_1473_);
    v___x_1480_ = l_Lean_mkConst(v_declName_1474_, v___x_1475_);
    crate::leanh::lean_inc_ref_n(v_type_1476_, 2);
    v___x_1481_ = l_Lean_mkApp4(
        v___x_1480_,
        v_type_1476_,
        v_type_1476_,
        v_type_1476_,
        v_inst_1477_,
    );
    v___x_1482_ = crate::leanh::lean_apply_1(v_canonExpr_1479_, v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(
    mut v_inst_1483_: *mut crate::leanh::LeanObject,
    mut v_declName_1484_: *mut crate::leanh::LeanObject,
    mut v___x_1485_: *mut crate::leanh::LeanObject,
    mut v_type_1486_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1487_: *mut crate::leanh::LeanObject,
    mut v_inst_1488_: *mut crate::leanh::LeanObject,
    mut v_toBind_1489_: *mut crate::leanh::LeanObject,
    mut v_inst_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_1490_);
    crate::leanh::lean_inc(v_declName_1484_);
    v___f_1491_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1491_, 0, v_inst_1483_);
    crate::leanh::lean_closure_set(v___f_1491_, 1, v_declName_1484_);
    crate::leanh::lean_closure_set(v___f_1491_, 2, v___x_1485_);
    crate::leanh::lean_closure_set(v___f_1491_, 3, v_type_1486_);
    crate::leanh::lean_closure_set(v___f_1491_, 4, v_inst_1490_);
    v___x_1492_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1492_, 0, v_declName_1484_);
    crate::leanh::lean_closure_set(v___x_1492_, 1, v_inst_1490_);
    crate::leanh::lean_closure_set(v___x_1492_, 2, v_expectedInst_1487_);
    v___x_1493_ = crate::leanh::lean_apply_2(v_inst_1488_, crate::leanh::lean_box(0), v___x_1492_);
    v___x_1494_ = crate::leanh::lean_apply_4(
        v_toBind_1489_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1493_,
        v___f_1491_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
    mut v_inst_1495_: *mut crate::leanh::LeanObject,
    mut v_inst_1496_: *mut crate::leanh::LeanObject,
    mut v_inst_1497_: *mut crate::leanh::LeanObject,
    mut v_inst_1498_: *mut crate::leanh::LeanObject,
    mut v_type_1499_: *mut crate::leanh::LeanObject,
    mut v_u_1500_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1501_: *mut crate::leanh::LeanObject,
    mut v_declName_1502_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1504_ = crate::leanh::lean_ctor_get(v_inst_1497_, 1);
    crate::leanh::lean_inc_n(v_toBind_1504_, 2);
    v___x_1505_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_n(v_u_1500_, 2);
    v___x_1506_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1506_, 0, v_u_1500_);
    crate::leanh::lean_ctor_set(v___x_1506_, 1, v___x_1505_);
    v___x_1507_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1507_, 0, v_u_1500_);
    crate::leanh::lean_ctor_set(v___x_1507_, 1, v___x_1506_);
    v___x_1508_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1508_, 0, v_u_1500_);
    crate::leanh::lean_ctor_set(v___x_1508_, 1, v___x_1507_);
    crate::leanh::lean_inc_ref_n(v_type_1499_, 3);
    crate::leanh::lean_inc_ref(v___x_1508_);
    crate::leanh::lean_inc_ref(v_inst_1498_);
    v___f_1509_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1509_, 0, v_inst_1498_);
    crate::leanh::lean_closure_set(v___f_1509_, 1, v_declName_1502_);
    crate::leanh::lean_closure_set(v___f_1509_, 2, v___x_1508_);
    crate::leanh::lean_closure_set(v___f_1509_, 3, v_type_1499_);
    crate::leanh::lean_closure_set(v___f_1509_, 4, v_expectedInst_1503_);
    crate::leanh::lean_closure_set(v___f_1509_, 5, v_inst_1495_);
    crate::leanh::lean_closure_set(v___f_1509_, 6, v_toBind_1504_);
    v___x_1510_ = l_Lean_mkConst(v_instDeclName_1501_, v___x_1508_);
    v___x_1511_ = l_Lean_mkApp3(v___x_1510_, v_type_1499_, v_type_1499_, v_type_1499_);
    v___x_1512_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1497_,
        v_inst_1496_,
        v_inst_1498_,
        v___x_1511_,
    );
    v___x_1513_ = crate::leanh::lean_apply_4(
        v_toBind_1504_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1512_,
        v___f_1509_,
    );
    return v___x_1513_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn(
    mut v_m_1514_: *mut crate::leanh::LeanObject,
    mut v_inst_1515_: *mut crate::leanh::LeanObject,
    mut v_inst_1516_: *mut crate::leanh::LeanObject,
    mut v_inst_1517_: *mut crate::leanh::LeanObject,
    mut v_inst_1518_: *mut crate::leanh::LeanObject,
    mut v_type_1519_: *mut crate::leanh::LeanObject,
    mut v_u_1520_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_1521_: *mut crate::leanh::LeanObject,
    mut v_declName_1522_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_1525_: *mut crate::leanh::LeanObject,
    mut v___x_1526_: *mut crate::leanh::LeanObject,
    mut v___x_1527_: *mut crate::leanh::LeanObject,
    mut v_type_1528_: *mut crate::leanh::LeanObject,
    mut v___x_1529_: *mut crate::leanh::LeanObject,
    mut v_inst_1530_: *mut crate::leanh::LeanObject,
    mut v_____r_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1532_ = crate::leanh::lean_ctor_get(v_inst_1525_, 0);
    crate::leanh::lean_inc(v_canonExpr_1532_);
    crate::leanh::lean_dec_ref(v_inst_1525_);
    v___x_1533_ = l_Lean_mkConst(v___x_1526_, v___x_1527_);
    crate::leanh::lean_inc_ref(v_type_1528_);
    v___x_1534_ = l_Lean_mkApp4(
        v___x_1533_,
        v_type_1528_,
        v___x_1529_,
        v_type_1528_,
        v_inst_1530_,
    );
    v___x_1535_ = crate::leanh::lean_apply_1(v_canonExpr_1532_, v___x_1534_);
    return v___x_1535_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(
    mut v___x_1546_: *mut crate::leanh::LeanObject,
    mut v_type_1547_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1548_: *mut crate::leanh::LeanObject,
    mut v___x_1549_: *mut crate::leanh::LeanObject,
    mut v_inst_1550_: *mut crate::leanh::LeanObject,
    mut v___x_1551_: *mut crate::leanh::LeanObject,
    mut v___x_1552_: *mut crate::leanh::LeanObject,
    mut v_inst_1553_: *mut crate::leanh::LeanObject,
    mut v_toBind_1554_: *mut crate::leanh::LeanObject,
    mut v_inst_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4;
    v___x_1557_ = l_Lean_mkConst(v___x_1556_, v___x_1546_);
    crate::leanh::lean_inc_ref(v_type_1547_);
    v_inst_x27_1558_ = l_Lean_mkAppB(v___x_1557_, v_type_1547_, v_semiringInst_1548_);
    v___x_1559_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5;
    v___x_1560_ = l_Lean_Name_mkStr2(v___x_1549_, v___x_1559_);
    crate::leanh::lean_inc_ref(v_inst_1555_);
    crate::leanh::lean_inc(v___x_1560_);
    v___f_1561_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1561_, 0, v_inst_1550_);
    crate::leanh::lean_closure_set(v___f_1561_, 1, v___x_1560_);
    crate::leanh::lean_closure_set(v___f_1561_, 2, v___x_1551_);
    crate::leanh::lean_closure_set(v___f_1561_, 3, v_type_1547_);
    crate::leanh::lean_closure_set(v___f_1561_, 4, v___x_1552_);
    crate::leanh::lean_closure_set(v___f_1561_, 5, v_inst_1555_);
    v___x_1562_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1562_, 0, v___x_1560_);
    crate::leanh::lean_closure_set(v___x_1562_, 1, v_inst_1555_);
    crate::leanh::lean_closure_set(v___x_1562_, 2, v_inst_x27_1558_);
    v___x_1563_ = crate::leanh::lean_apply_2(v_inst_1553_, crate::leanh::lean_box(0), v___x_1562_);
    v___x_1564_ = crate::leanh::lean_apply_4(
        v_toBind_1554_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1563_,
        v___f_1561_,
    );
    return v___x_1564_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1569_ = l_Lean_Level_ofNat(v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
    mut v_inst_1570_: *mut crate::leanh::LeanObject,
    mut v_inst_1571_: *mut crate::leanh::LeanObject,
    mut v_inst_1572_: *mut crate::leanh::LeanObject,
    mut v_inst_1573_: *mut crate::leanh::LeanObject,
    mut v_u_1574_: *mut crate::leanh::LeanObject,
    mut v_type_1575_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1577_ = crate::leanh::lean_ctor_get(v_inst_1572_, 1);
    crate::leanh::lean_inc_n(v_toBind_1577_, 2);
    v___x_1578_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0;
    v___x_1579_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1;
    v___x_1580_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2,
    );
    v___x_1581_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_u_1574_);
    v___x_1582_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1582_, 0, v_u_1574_);
    crate::leanh::lean_ctor_set(v___x_1582_, 1, v___x_1581_);
    crate::leanh::lean_inc_ref(v___x_1582_);
    v___x_1583_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1583_, 0, v___x_1580_);
    crate::leanh::lean_ctor_set(v___x_1583_, 1, v___x_1582_);
    v___x_1584_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1584_, 0, v_u_1574_);
    crate::leanh::lean_ctor_set(v___x_1584_, 1, v___x_1583_);
    crate::leanh::lean_inc_ref(v___x_1584_);
    v___x_1585_ = l_Lean_mkConst(v___x_1579_, v___x_1584_);
    v___x_1586_ = l_Lean_Nat_mkType;
    crate::leanh::lean_inc_ref(v_inst_1573_);
    crate::leanh::lean_inc_ref_n(v_type_1575_, 2);
    v___f_1587_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        10,
        9,
    );
    crate::leanh::lean_closure_set(v___f_1587_, 0, v___x_1582_);
    crate::leanh::lean_closure_set(v___f_1587_, 1, v_type_1575_);
    crate::leanh::lean_closure_set(v___f_1587_, 2, v_semiringInst_1576_);
    crate::leanh::lean_closure_set(v___f_1587_, 3, v___x_1578_);
    crate::leanh::lean_closure_set(v___f_1587_, 4, v_inst_1573_);
    crate::leanh::lean_closure_set(v___f_1587_, 5, v___x_1584_);
    crate::leanh::lean_closure_set(v___f_1587_, 6, v___x_1586_);
    crate::leanh::lean_closure_set(v___f_1587_, 7, v_inst_1570_);
    crate::leanh::lean_closure_set(v___f_1587_, 8, v_toBind_1577_);
    v___x_1588_ = l_Lean_mkApp3(v___x_1585_, v_type_1575_, v___x_1586_, v_type_1575_);
    v___x_1589_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1572_,
        v_inst_1571_,
        v_inst_1573_,
        v___x_1588_,
    );
    v___x_1590_ = crate::leanh::lean_apply_4(
        v_toBind_1577_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1589_,
        v___f_1587_,
    );
    return v___x_1590_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn(
    mut v_m_1591_: *mut crate::leanh::LeanObject,
    mut v_inst_1592_: *mut crate::leanh::LeanObject,
    mut v_inst_1593_: *mut crate::leanh::LeanObject,
    mut v_inst_1594_: *mut crate::leanh::LeanObject,
    mut v_inst_1595_: *mut crate::leanh::LeanObject,
    mut v_u_1596_: *mut crate::leanh::LeanObject,
    mut v_type_1597_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_1600_: *mut crate::leanh::LeanObject,
    mut v___x_1601_: *mut crate::leanh::LeanObject,
    mut v___x_1602_: *mut crate::leanh::LeanObject,
    mut v_type_1603_: *mut crate::leanh::LeanObject,
    mut v_canonExpr_1604_: *mut crate::leanh::LeanObject,
    mut v_inst_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Name_mkStr2(v___x_1600_, v___x_1601_);
    v___x_1607_ = l_Lean_mkConst(v___x_1606_, v___x_1602_);
    v___x_1608_ = l_Lean_mkAppB(v___x_1607_, v_type_1603_, v_inst_1605_);
    v___x_1609_ = crate::leanh::lean_apply_1(v_canonExpr_1604_, v___x_1608_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1(
    mut v___f_1610_: *mut crate::leanh::LeanObject,
    mut v_inst_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1612_ = crate::leanh::lean_apply_1(v___f_1610_, v_inst_1611_);
    return v___x_1612_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3(
    mut v_toPure_1613_: *mut crate::leanh::LeanObject,
    mut v_val_1614_: *mut crate::leanh::LeanObject,
    mut v_toBind_1615_: *mut crate::leanh::LeanObject,
    mut v___f_1616_: *mut crate::leanh::LeanObject,
    mut v_____r_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ =
        crate::leanh::lean_apply_2(v_toPure_1613_, crate::leanh::lean_box(0), v_val_1614_);
    v___x_1619_ = crate::leanh::lean_apply_4(
        v_toBind_1615_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1618_,
        v___f_1616_,
    );
    return v___x_1619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2(
    mut v_toPure_1620_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_1621_: *mut crate::leanh::LeanObject,
    mut v_toBind_1622_: *mut crate::leanh::LeanObject,
    mut v___f_1623_: *mut crate::leanh::LeanObject,
    mut v___f_1624_: *mut crate::leanh::LeanObject,
    mut v___x_1625_: *mut crate::leanh::LeanObject,
    mut v___x_1626_: *mut crate::leanh::LeanObject,
    mut v_inst_1627_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1628_) == 0 {
        let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_1627_);
        crate::leanh::lean_dec_ref(v___x_1626_);
        crate::leanh::lean_dec_ref(v___x_1625_);
        crate::leanh::lean_dec(v___f_1624_);
        v___x_1629_ =
            crate::leanh::lean_apply_2(v_toPure_1620_, crate::leanh::lean_box(0), v_inst_x27_1621_);
        v___x_1630_ = crate::leanh::lean_apply_4(
            v_toBind_1622_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1629_,
            v___f_1623_,
        );
        return v___x_1630_;
    } else {
        let mut v_val_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_1623_);
        v_val_1631_ = crate::leanh::lean_ctor_get(v_____do__lift_1628_, 0);
        crate::leanh::lean_inc_n(v_val_1631_, 2);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1628_, 1);
        crate::leanh::lean_inc(v_toBind_1622_);
        v___f_1632_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1632_, 0, v_toPure_1620_);
        crate::leanh::lean_closure_set(v___f_1632_, 1, v_val_1631_);
        crate::leanh::lean_closure_set(v___f_1632_, 2, v_toBind_1622_);
        crate::leanh::lean_closure_set(v___f_1632_, 3, v___f_1624_);
        v___x_1633_ = l_Lean_Name_mkStr2(v___x_1625_, v___x_1626_);
        v___x_1634_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        crate::leanh::lean_closure_set(v___x_1634_, 0, v___x_1633_);
        crate::leanh::lean_closure_set(v___x_1634_, 1, v_val_1631_);
        crate::leanh::lean_closure_set(v___x_1634_, 2, v_inst_x27_1621_);
        v___x_1635_ =
            crate::leanh::lean_apply_2(v_inst_1627_, crate::leanh::lean_box(0), v___x_1634_);
        v___x_1636_ = crate::leanh::lean_apply_4(
            v_toBind_1622_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1635_,
            v___f_1632_,
        );
        return v___x_1636_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
    mut v_inst_1646_: *mut crate::leanh::LeanObject,
    mut v_inst_1647_: *mut crate::leanh::LeanObject,
    mut v_inst_1648_: *mut crate::leanh::LeanObject,
    mut v_u_1649_: *mut crate::leanh::LeanObject,
    mut v_type_1650_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v_toPure_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instType_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1652_ = crate::leanh::lean_ctor_get(v_inst_1647_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1652_);
                v_toBind_1653_ = crate::leanh::lean_ctor_get(v_inst_1647_, 1);
                crate::leanh::lean_inc(v_toBind_1653_);
                crate::leanh::lean_dec_ref(v_inst_1647_);
                v_canonExpr_1654_ = crate::leanh::lean_ctor_get(v_inst_1648_, 0);
                v_synthInstance_x3f_1655_ = crate::leanh::lean_ctor_get(v_inst_1648_, 1);
                v_isSharedCheck_1677_ = (!crate::leanh::lean_is_exclusive(v_inst_1648_)) as u8;
                if v_isSharedCheck_1677_ == 0 {
                    v___x_1657_ = v_inst_1648_;
                    v_isShared_1658_ = v_isSharedCheck_1677_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_synthInstance_x3f_1655_);
                    crate::leanh::lean_inc(v_canonExpr_1654_);
                    crate::leanh::lean_dec(v_inst_1648_);
                    v___x_1657_ = crate::leanh::lean_box(0);
                    v_isShared_1658_ = v_isSharedCheck_1677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1659_ = crate::leanh::lean_ctor_get(v_toApplicative_1652_, 1);
                crate::leanh::lean_inc(v_toPure_1659_);
                crate::leanh::lean_dec_ref(v_toApplicative_1652_);
                v___x_1660_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0;
                v___x_1661_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1;
                v___x_1662_ = crate::leanh::lean_box(0);
                if v_isShared_1658_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1657_, 1);
                    crate::leanh::lean_ctor_set(v___x_1657_, 1, v___x_1662_);
                    crate::leanh::lean_ctor_set(v___x_1657_, 0, v_u_1649_);
                    v___x_1664_ = v___x_1657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_u_1649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1662_);
                    v___x_1664_ = v_reuseFailAlloc_1676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___x_1664_, 2);
                v___x_1665_ = l_Lean_mkConst(v___x_1661_, v___x_1664_);
                crate::leanh::lean_inc_ref_n(v_type_1650_, 2);
                v_inst_x27_1666_ = l_Lean_mkAppB(v___x_1665_, v_type_1650_, v_semiringInst_1651_);
                v___x_1667_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2;
                v___f_1668_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_1668_, 0, v___x_1667_);
                crate::leanh::lean_closure_set(v___f_1668_, 1, v___x_1660_);
                crate::leanh::lean_closure_set(v___f_1668_, 2, v___x_1664_);
                crate::leanh::lean_closure_set(v___f_1668_, 3, v_type_1650_);
                crate::leanh::lean_closure_set(v___f_1668_, 4, v_canonExpr_1654_);
                v___f_1669_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1669_, 0, v___f_1668_);
                v___x_1670_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3;
                v___x_1671_ = l_Lean_mkConst(v___x_1670_, v___x_1664_);
                v_instType_1672_ = l_Lean_Expr_app___override(v___x_1671_, v_type_1650_);
                v___x_1673_ =
                    crate::leanh::lean_apply_1(v_synthInstance_x3f_1655_, v_instType_1672_);
                crate::leanh::lean_inc_ref(v___f_1669_);
                crate::leanh::lean_inc(v_toBind_1653_);
                v___f_1674_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2
                        as *mut core::ffi::c_void,
                    9,
                    8,
                );
                crate::leanh::lean_closure_set(v___f_1674_, 0, v_toPure_1659_);
                crate::leanh::lean_closure_set(v___f_1674_, 1, v_inst_x27_1666_);
                crate::leanh::lean_closure_set(v___f_1674_, 2, v_toBind_1653_);
                crate::leanh::lean_closure_set(v___f_1674_, 3, v___f_1669_);
                crate::leanh::lean_closure_set(v___f_1674_, 4, v___f_1669_);
                crate::leanh::lean_closure_set(v___f_1674_, 5, v___x_1667_);
                crate::leanh::lean_closure_set(v___f_1674_, 6, v___x_1660_);
                crate::leanh::lean_closure_set(v___f_1674_, 7, v_inst_1646_);
                v___x_1675_ = crate::leanh::lean_apply_4(
                    v_toBind_1653_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_m_1678_: *mut crate::leanh::LeanObject,
    mut v_inst_1679_: *mut crate::leanh::LeanObject,
    mut v_inst_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
    mut v_u_1682_: *mut crate::leanh::LeanObject,
    mut v_type_1683_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_addFn_1686_: *mut crate::leanh::LeanObject,
    mut v_s_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v_unused_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1688_ = crate::leanh::lean_ctor_get(v_s_1687_, 0);
                v_type_1689_ = crate::leanh::lean_ctor_get(v_s_1687_, 1);
                v_u_1690_ = crate::leanh::lean_ctor_get(v_s_1687_, 2);
                v_ringInst_1691_ = crate::leanh::lean_ctor_get(v_s_1687_, 3);
                v_semiringInst_1692_ = crate::leanh::lean_ctor_get(v_s_1687_, 4);
                v_charInst_x3f_1693_ = crate::leanh::lean_ctor_get(v_s_1687_, 5);
                v_mulFn_x3f_1694_ = crate::leanh::lean_ctor_get(v_s_1687_, 7);
                v_subFn_x3f_1695_ = crate::leanh::lean_ctor_get(v_s_1687_, 8);
                v_negFn_x3f_1696_ = crate::leanh::lean_ctor_get(v_s_1687_, 9);
                v_powFn_x3f_1697_ = crate::leanh::lean_ctor_get(v_s_1687_, 10);
                v_intCastFn_x3f_1698_ = crate::leanh::lean_ctor_get(v_s_1687_, 11);
                v_natCastFn_x3f_1699_ = crate::leanh::lean_ctor_get(v_s_1687_, 12);
                v_one_x3f_1700_ = crate::leanh::lean_ctor_get(v_s_1687_, 13);
                v_vars_1701_ = crate::leanh::lean_ctor_get(v_s_1687_, 14);
                v_varMap_1702_ = crate::leanh::lean_ctor_get(v_s_1687_, 15);
                v_denote_1703_ = crate::leanh::lean_ctor_get(v_s_1687_, 16);
                v_isSharedCheck_1711_ = (!crate::leanh::lean_is_exclusive(v_s_1687_)) as u8;
                if v_isSharedCheck_1711_ == 0 {
                    v_unused_1712_ = crate::leanh::lean_ctor_get(v_s_1687_, 6);
                    crate::leanh::lean_dec(v_unused_1712_);
                    v___x_1705_ = v_s_1687_;
                    v_isShared_1706_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_1703_);
                    crate::leanh::lean_inc(v_varMap_1702_);
                    crate::leanh::lean_inc(v_vars_1701_);
                    crate::leanh::lean_inc(v_one_x3f_1700_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_1699_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_1698_);
                    crate::leanh::lean_inc(v_powFn_x3f_1697_);
                    crate::leanh::lean_inc(v_negFn_x3f_1696_);
                    crate::leanh::lean_inc(v_subFn_x3f_1695_);
                    crate::leanh::lean_inc(v_mulFn_x3f_1694_);
                    crate::leanh::lean_inc(v_charInst_x3f_1693_);
                    crate::leanh::lean_inc(v_semiringInst_1692_);
                    crate::leanh::lean_inc(v_ringInst_1691_);
                    crate::leanh::lean_inc(v_u_1690_);
                    crate::leanh::lean_inc(v_type_1689_);
                    crate::leanh::lean_inc(v_id_1688_);
                    crate::leanh::lean_dec(v_s_1687_);
                    v___x_1705_ = crate::leanh::lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1707_, 0, v_addFn_1686_);
                if v_isShared_1706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1705_, 6, v___x_1707_);
                    v___x_1709_ = v___x_1705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_id_1688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_type_1689_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_u_1690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_ringInst_1691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_semiringInst_1692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 5, v_charInst_x3f_1693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 6, v___x_1707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 7, v_mulFn_x3f_1694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 8, v_subFn_x3f_1695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 9, v_negFn_x3f_1696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 10, v_powFn_x3f_1697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 11, v_intCastFn_x3f_1698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 12, v_natCastFn_x3f_1699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 13, v_one_x3f_1700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 14, v_vars_1701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 15, v_varMap_1702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 16, v_denote_1703_);
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
    mut v_toPure_1713_: *mut crate::leanh::LeanObject,
    mut v_addFn_1714_: *mut crate::leanh::LeanObject,
    mut v_____r_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ =
        crate::leanh::lean_apply_2(v_toPure_1713_, crate::leanh::lean_box(0), v_addFn_1714_);
    return v___x_1716_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2(
    mut v_toPure_1717_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_1718_: *mut crate::leanh::LeanObject,
    mut v_toBind_1719_: *mut crate::leanh::LeanObject,
    mut v_addFn_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_addFn_1720_);
    v___f_1721_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1721_, 0, v_addFn_1720_);
    v___f_1722_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1722_, 0, v_toPure_1717_);
    crate::leanh::lean_closure_set(v___f_1722_, 1, v_addFn_1720_);
    v___x_1723_ = crate::leanh::lean_apply_1(v_modifyRing_1718_, v___f_1721_);
    v___x_1724_ = crate::leanh::lean_apply_4(
        v_toBind_1719_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1723_,
        v___f_1722_,
    );
    return v___x_1724_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(
    mut v_toPure_1741_: *mut crate::leanh::LeanObject,
    mut v_inst_1742_: *mut crate::leanh::LeanObject,
    mut v_inst_1743_: *mut crate::leanh::LeanObject,
    mut v_inst_1744_: *mut crate::leanh::LeanObject,
    mut v_inst_1745_: *mut crate::leanh::LeanObject,
    mut v_toBind_1746_: *mut crate::leanh::LeanObject,
    mut v___f_1747_: *mut crate::leanh::LeanObject,
    mut v_ring_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_addFn_x3f_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_addFn_x3f_1749_ = crate::leanh::lean_ctor_get(v_ring_1748_, 6);
    if crate::leanh::lean_obj_tag(v_addFn_x3f_1749_) == 1 {
        let mut v_val_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_addFn_x3f_1749_);
        crate::leanh::lean_dec_ref(v_ring_1748_);
        crate::leanh::lean_dec(v___f_1747_);
        crate::leanh::lean_dec(v_toBind_1746_);
        crate::leanh::lean_dec_ref(v_inst_1745_);
        crate::leanh::lean_dec_ref(v_inst_1744_);
        crate::leanh::lean_dec_ref(v_inst_1743_);
        crate::leanh::lean_dec(v_inst_1742_);
        v_val_1750_ = crate::leanh::lean_ctor_get(v_addFn_x3f_1749_, 0);
        crate::leanh::lean_inc(v_val_1750_);
        crate::leanh::lean_dec_ref_known(v_addFn_x3f_1749_, 1);
        v___x_1751_ =
            crate::leanh::lean_apply_2(v_toPure_1741_, crate::leanh::lean_box(0), v_val_1750_);
        return v___x_1751_;
    } else {
        let mut v_type_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1741_);
        v_type_1752_ = crate::leanh::lean_ctor_get(v_ring_1748_, 1);
        crate::leanh::lean_inc_ref_n(v_type_1752_, 3);
        v_u_1753_ = crate::leanh::lean_ctor_get(v_ring_1748_, 2);
        crate::leanh::lean_inc_n(v_u_1753_, 2);
        v_semiringInst_1754_ = crate::leanh::lean_ctor_get(v_ring_1748_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_1754_);
        crate::leanh::lean_dec_ref(v_ring_1748_);
        v___x_1755_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1;
        v___x_1756_ = crate::leanh::lean_box(0);
        v___x_1757_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1757_, 0, v_u_1753_);
        crate::leanh::lean_ctor_set(v___x_1757_, 1, v___x_1756_);
        crate::leanh::lean_inc_ref(v___x_1757_);
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
        v___x_1766_ = crate::leanh::lean_apply_4(
            v_toBind_1746_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1765_,
            v___f_1747_,
        );
        return v___x_1766_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
    mut v_inst_1767_: *mut crate::leanh::LeanObject,
    mut v_inst_1768_: *mut crate::leanh::LeanObject,
    mut v_inst_1769_: *mut crate::leanh::LeanObject,
    mut v_inst_1770_: *mut crate::leanh::LeanObject,
    mut v_inst_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1772_ = crate::leanh::lean_ctor_get(v_inst_1769_, 0);
    v_toBind_1773_ = crate::leanh::lean_ctor_get(v_inst_1769_, 1);
    crate::leanh::lean_inc_n(v_toBind_1773_, 3);
    v_getRing_1774_ = crate::leanh::lean_ctor_get(v_inst_1771_, 0);
    crate::leanh::lean_inc(v_getRing_1774_);
    v_modifyRing_1775_ = crate::leanh::lean_ctor_get(v_inst_1771_, 1);
    crate::leanh::lean_inc(v_modifyRing_1775_);
    crate::leanh::lean_dec_ref(v_inst_1771_);
    v_toPure_1776_ = crate::leanh::lean_ctor_get(v_toApplicative_1772_, 1);
    crate::leanh::lean_inc_n(v_toPure_1776_, 2);
    v___f_1777_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1777_, 0, v_toPure_1776_);
    crate::leanh::lean_closure_set(v___f_1777_, 1, v_modifyRing_1775_);
    crate::leanh::lean_closure_set(v___f_1777_, 2, v_toBind_1773_);
    v___f_1778_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1778_, 0, v_toPure_1776_);
    crate::leanh::lean_closure_set(v___f_1778_, 1, v_inst_1767_);
    crate::leanh::lean_closure_set(v___f_1778_, 2, v_inst_1768_);
    crate::leanh::lean_closure_set(v___f_1778_, 3, v_inst_1769_);
    crate::leanh::lean_closure_set(v___f_1778_, 4, v_inst_1770_);
    crate::leanh::lean_closure_set(v___f_1778_, 5, v_toBind_1773_);
    crate::leanh::lean_closure_set(v___f_1778_, 6, v___f_1777_);
    v___x_1779_ = crate::leanh::lean_apply_4(
        v_toBind_1773_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_1774_,
        v___f_1778_,
    );
    return v___x_1779_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn(
    mut v_m_1780_: *mut crate::leanh::LeanObject,
    mut v_inst_1781_: *mut crate::leanh::LeanObject,
    mut v_inst_1782_: *mut crate::leanh::LeanObject,
    mut v_inst_1783_: *mut crate::leanh::LeanObject,
    mut v_inst_1784_: *mut crate::leanh::LeanObject,
    mut v_inst_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_subFn_1787_: *mut crate::leanh::LeanObject,
    mut v_s_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1789_ = crate::leanh::lean_ctor_get(v_s_1788_, 0);
                v_type_1790_ = crate::leanh::lean_ctor_get(v_s_1788_, 1);
                v_u_1791_ = crate::leanh::lean_ctor_get(v_s_1788_, 2);
                v_ringInst_1792_ = crate::leanh::lean_ctor_get(v_s_1788_, 3);
                v_semiringInst_1793_ = crate::leanh::lean_ctor_get(v_s_1788_, 4);
                v_charInst_x3f_1794_ = crate::leanh::lean_ctor_get(v_s_1788_, 5);
                v_addFn_x3f_1795_ = crate::leanh::lean_ctor_get(v_s_1788_, 6);
                v_mulFn_x3f_1796_ = crate::leanh::lean_ctor_get(v_s_1788_, 7);
                v_negFn_x3f_1797_ = crate::leanh::lean_ctor_get(v_s_1788_, 9);
                v_powFn_x3f_1798_ = crate::leanh::lean_ctor_get(v_s_1788_, 10);
                v_intCastFn_x3f_1799_ = crate::leanh::lean_ctor_get(v_s_1788_, 11);
                v_natCastFn_x3f_1800_ = crate::leanh::lean_ctor_get(v_s_1788_, 12);
                v_one_x3f_1801_ = crate::leanh::lean_ctor_get(v_s_1788_, 13);
                v_vars_1802_ = crate::leanh::lean_ctor_get(v_s_1788_, 14);
                v_varMap_1803_ = crate::leanh::lean_ctor_get(v_s_1788_, 15);
                v_denote_1804_ = crate::leanh::lean_ctor_get(v_s_1788_, 16);
                v_isSharedCheck_1812_ = (!crate::leanh::lean_is_exclusive(v_s_1788_)) as u8;
                if v_isSharedCheck_1812_ == 0 {
                    v_unused_1813_ = crate::leanh::lean_ctor_get(v_s_1788_, 8);
                    crate::leanh::lean_dec(v_unused_1813_);
                    v___x_1806_ = v_s_1788_;
                    v_isShared_1807_ = v_isSharedCheck_1812_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_1804_);
                    crate::leanh::lean_inc(v_varMap_1803_);
                    crate::leanh::lean_inc(v_vars_1802_);
                    crate::leanh::lean_inc(v_one_x3f_1801_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_1800_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_1799_);
                    crate::leanh::lean_inc(v_powFn_x3f_1798_);
                    crate::leanh::lean_inc(v_negFn_x3f_1797_);
                    crate::leanh::lean_inc(v_mulFn_x3f_1796_);
                    crate::leanh::lean_inc(v_addFn_x3f_1795_);
                    crate::leanh::lean_inc(v_charInst_x3f_1794_);
                    crate::leanh::lean_inc(v_semiringInst_1793_);
                    crate::leanh::lean_inc(v_ringInst_1792_);
                    crate::leanh::lean_inc(v_u_1791_);
                    crate::leanh::lean_inc(v_type_1790_);
                    crate::leanh::lean_inc(v_id_1789_);
                    crate::leanh::lean_dec(v_s_1788_);
                    v___x_1806_ = crate::leanh::lean_box(0);
                    v_isShared_1807_ = v_isSharedCheck_1812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1808_, 0, v_subFn_1787_);
                if v_isShared_1807_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1806_, 8, v___x_1808_);
                    v___x_1810_ = v___x_1806_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_id_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_type_1790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_u_1791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_ringInst_1792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 4, v_semiringInst_1793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 5, v_charInst_x3f_1794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 6, v_addFn_x3f_1795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 7, v_mulFn_x3f_1796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 8, v___x_1808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 9, v_negFn_x3f_1797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 10, v_powFn_x3f_1798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 11, v_intCastFn_x3f_1799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 12, v_natCastFn_x3f_1800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 13, v_one_x3f_1801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 14, v_vars_1802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 15, v_varMap_1803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 16, v_denote_1804_);
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
    mut v_toPure_1814_: *mut crate::leanh::LeanObject,
    mut v_subFn_1815_: *mut crate::leanh::LeanObject,
    mut v_____r_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ =
        crate::leanh::lean_apply_2(v_toPure_1814_, crate::leanh::lean_box(0), v_subFn_1815_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2(
    mut v_toPure_1818_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_1819_: *mut crate::leanh::LeanObject,
    mut v_toBind_1820_: *mut crate::leanh::LeanObject,
    mut v_subFn_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_subFn_1821_);
    v___f_1822_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1822_, 0, v_subFn_1821_);
    v___f_1823_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1823_, 0, v_toPure_1818_);
    crate::leanh::lean_closure_set(v___f_1823_, 1, v_subFn_1821_);
    v___x_1824_ = crate::leanh::lean_apply_1(v_modifyRing_1819_, v___f_1822_);
    v___x_1825_ = crate::leanh::lean_apply_4(
        v_toBind_1820_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1824_,
        v___f_1823_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(
    mut v_toPure_1843_: *mut crate::leanh::LeanObject,
    mut v_inst_1844_: *mut crate::leanh::LeanObject,
    mut v_inst_1845_: *mut crate::leanh::LeanObject,
    mut v_inst_1846_: *mut crate::leanh::LeanObject,
    mut v_inst_1847_: *mut crate::leanh::LeanObject,
    mut v_toBind_1848_: *mut crate::leanh::LeanObject,
    mut v___f_1849_: *mut crate::leanh::LeanObject,
    mut v_ring_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subFn_x3f_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_subFn_x3f_1851_ = crate::leanh::lean_ctor_get(v_ring_1850_, 8);
    if crate::leanh::lean_obj_tag(v_subFn_x3f_1851_) == 1 {
        let mut v_val_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_subFn_x3f_1851_);
        crate::leanh::lean_dec_ref(v_ring_1850_);
        crate::leanh::lean_dec(v___f_1849_);
        crate::leanh::lean_dec(v_toBind_1848_);
        crate::leanh::lean_dec_ref(v_inst_1847_);
        crate::leanh::lean_dec_ref(v_inst_1846_);
        crate::leanh::lean_dec_ref(v_inst_1845_);
        crate::leanh::lean_dec(v_inst_1844_);
        v_val_1852_ = crate::leanh::lean_ctor_get(v_subFn_x3f_1851_, 0);
        crate::leanh::lean_inc(v_val_1852_);
        crate::leanh::lean_dec_ref_known(v_subFn_x3f_1851_, 1);
        v___x_1853_ =
            crate::leanh::lean_apply_2(v_toPure_1843_, crate::leanh::lean_box(0), v_val_1852_);
        return v___x_1853_;
    } else {
        let mut v_type_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ringInst_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1843_);
        v_type_1854_ = crate::leanh::lean_ctor_get(v_ring_1850_, 1);
        crate::leanh::lean_inc_ref_n(v_type_1854_, 3);
        v_u_1855_ = crate::leanh::lean_ctor_get(v_ring_1850_, 2);
        crate::leanh::lean_inc_n(v_u_1855_, 2);
        v_ringInst_1856_ = crate::leanh::lean_ctor_get(v_ring_1850_, 3);
        crate::leanh::lean_inc_ref(v_ringInst_1856_);
        crate::leanh::lean_dec_ref(v_ring_1850_);
        v___x_1857_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1;
        v___x_1858_ = crate::leanh::lean_box(0);
        v___x_1859_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1859_, 0, v_u_1855_);
        crate::leanh::lean_ctor_set(v___x_1859_, 1, v___x_1858_);
        crate::leanh::lean_inc_ref(v___x_1859_);
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
        v___x_1868_ = crate::leanh::lean_apply_4(
            v_toBind_1848_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1867_,
            v___f_1849_,
        );
        return v___x_1868_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(
    mut v_inst_1869_: *mut crate::leanh::LeanObject,
    mut v_inst_1870_: *mut crate::leanh::LeanObject,
    mut v_inst_1871_: *mut crate::leanh::LeanObject,
    mut v_inst_1872_: *mut crate::leanh::LeanObject,
    mut v_inst_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1874_ = crate::leanh::lean_ctor_get(v_inst_1871_, 0);
    v_toBind_1875_ = crate::leanh::lean_ctor_get(v_inst_1871_, 1);
    crate::leanh::lean_inc_n(v_toBind_1875_, 3);
    v_getRing_1876_ = crate::leanh::lean_ctor_get(v_inst_1873_, 0);
    crate::leanh::lean_inc(v_getRing_1876_);
    v_modifyRing_1877_ = crate::leanh::lean_ctor_get(v_inst_1873_, 1);
    crate::leanh::lean_inc(v_modifyRing_1877_);
    crate::leanh::lean_dec_ref(v_inst_1873_);
    v_toPure_1878_ = crate::leanh::lean_ctor_get(v_toApplicative_1874_, 1);
    crate::leanh::lean_inc_n(v_toPure_1878_, 2);
    v___f_1879_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1879_, 0, v_toPure_1878_);
    crate::leanh::lean_closure_set(v___f_1879_, 1, v_modifyRing_1877_);
    crate::leanh::lean_closure_set(v___f_1879_, 2, v_toBind_1875_);
    v___f_1880_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1880_, 0, v_toPure_1878_);
    crate::leanh::lean_closure_set(v___f_1880_, 1, v_inst_1869_);
    crate::leanh::lean_closure_set(v___f_1880_, 2, v_inst_1870_);
    crate::leanh::lean_closure_set(v___f_1880_, 3, v_inst_1871_);
    crate::leanh::lean_closure_set(v___f_1880_, 4, v_inst_1872_);
    crate::leanh::lean_closure_set(v___f_1880_, 5, v_toBind_1875_);
    crate::leanh::lean_closure_set(v___f_1880_, 6, v___f_1879_);
    v___x_1881_ = crate::leanh::lean_apply_4(
        v_toBind_1875_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_1876_,
        v___f_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn(
    mut v_m_1882_: *mut crate::leanh::LeanObject,
    mut v_inst_1883_: *mut crate::leanh::LeanObject,
    mut v_inst_1884_: *mut crate::leanh::LeanObject,
    mut v_inst_1885_: *mut crate::leanh::LeanObject,
    mut v_inst_1886_: *mut crate::leanh::LeanObject,
    mut v_inst_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mulFn_1889_: *mut crate::leanh::LeanObject,
    mut v_s_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1914_: u8 = 0;
    let mut v_unused_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1891_ = crate::leanh::lean_ctor_get(v_s_1890_, 0);
                v_type_1892_ = crate::leanh::lean_ctor_get(v_s_1890_, 1);
                v_u_1893_ = crate::leanh::lean_ctor_get(v_s_1890_, 2);
                v_ringInst_1894_ = crate::leanh::lean_ctor_get(v_s_1890_, 3);
                v_semiringInst_1895_ = crate::leanh::lean_ctor_get(v_s_1890_, 4);
                v_charInst_x3f_1896_ = crate::leanh::lean_ctor_get(v_s_1890_, 5);
                v_addFn_x3f_1897_ = crate::leanh::lean_ctor_get(v_s_1890_, 6);
                v_subFn_x3f_1898_ = crate::leanh::lean_ctor_get(v_s_1890_, 8);
                v_negFn_x3f_1899_ = crate::leanh::lean_ctor_get(v_s_1890_, 9);
                v_powFn_x3f_1900_ = crate::leanh::lean_ctor_get(v_s_1890_, 10);
                v_intCastFn_x3f_1901_ = crate::leanh::lean_ctor_get(v_s_1890_, 11);
                v_natCastFn_x3f_1902_ = crate::leanh::lean_ctor_get(v_s_1890_, 12);
                v_one_x3f_1903_ = crate::leanh::lean_ctor_get(v_s_1890_, 13);
                v_vars_1904_ = crate::leanh::lean_ctor_get(v_s_1890_, 14);
                v_varMap_1905_ = crate::leanh::lean_ctor_get(v_s_1890_, 15);
                v_denote_1906_ = crate::leanh::lean_ctor_get(v_s_1890_, 16);
                v_isSharedCheck_1914_ = (!crate::leanh::lean_is_exclusive(v_s_1890_)) as u8;
                if v_isSharedCheck_1914_ == 0 {
                    v_unused_1915_ = crate::leanh::lean_ctor_get(v_s_1890_, 7);
                    crate::leanh::lean_dec(v_unused_1915_);
                    v___x_1908_ = v_s_1890_;
                    v_isShared_1909_ = v_isSharedCheck_1914_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_1906_);
                    crate::leanh::lean_inc(v_varMap_1905_);
                    crate::leanh::lean_inc(v_vars_1904_);
                    crate::leanh::lean_inc(v_one_x3f_1903_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_1902_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_1901_);
                    crate::leanh::lean_inc(v_powFn_x3f_1900_);
                    crate::leanh::lean_inc(v_negFn_x3f_1899_);
                    crate::leanh::lean_inc(v_subFn_x3f_1898_);
                    crate::leanh::lean_inc(v_addFn_x3f_1897_);
                    crate::leanh::lean_inc(v_charInst_x3f_1896_);
                    crate::leanh::lean_inc(v_semiringInst_1895_);
                    crate::leanh::lean_inc(v_ringInst_1894_);
                    crate::leanh::lean_inc(v_u_1893_);
                    crate::leanh::lean_inc(v_type_1892_);
                    crate::leanh::lean_inc(v_id_1891_);
                    crate::leanh::lean_dec(v_s_1890_);
                    v___x_1908_ = crate::leanh::lean_box(0);
                    v_isShared_1909_ = v_isSharedCheck_1914_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1910_, 0, v_mulFn_1889_);
                if v_isShared_1909_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1908_, 7, v___x_1910_);
                    v___x_1912_ = v___x_1908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_id_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_type_1892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_u_1893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_ringInst_1894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_semiringInst_1895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_charInst_x3f_1896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 6, v_addFn_x3f_1897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 7, v___x_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 8, v_subFn_x3f_1898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 9, v_negFn_x3f_1899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 10, v_powFn_x3f_1900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 11, v_intCastFn_x3f_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 12, v_natCastFn_x3f_1902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 13, v_one_x3f_1903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 14, v_vars_1904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 15, v_varMap_1905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 16, v_denote_1906_);
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
    mut v_toPure_1916_: *mut crate::leanh::LeanObject,
    mut v_mulFn_1917_: *mut crate::leanh::LeanObject,
    mut v_____r_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ =
        crate::leanh::lean_apply_2(v_toPure_1916_, crate::leanh::lean_box(0), v_mulFn_1917_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2(
    mut v_toPure_1920_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_1921_: *mut crate::leanh::LeanObject,
    mut v_toBind_1922_: *mut crate::leanh::LeanObject,
    mut v_mulFn_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_mulFn_1923_);
    v___f_1924_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1924_, 0, v_mulFn_1923_);
    v___f_1925_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1925_, 0, v_toPure_1920_);
    crate::leanh::lean_closure_set(v___f_1925_, 1, v_mulFn_1923_);
    v___x_1926_ = crate::leanh::lean_apply_1(v_modifyRing_1921_, v___f_1924_);
    v___x_1927_ = crate::leanh::lean_apply_4(
        v_toBind_1922_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1926_,
        v___f_1925_,
    );
    return v___x_1927_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(
    mut v_toPure_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_inst_1947_: *mut crate::leanh::LeanObject,
    mut v_inst_1948_: *mut crate::leanh::LeanObject,
    mut v_toBind_1949_: *mut crate::leanh::LeanObject,
    mut v___f_1950_: *mut crate::leanh::LeanObject,
    mut v_ring_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mulFn_x3f_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_1952_ = crate::leanh::lean_ctor_get(v_ring_1951_, 7);
    if crate::leanh::lean_obj_tag(v_mulFn_x3f_1952_) == 1 {
        let mut v_val_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_mulFn_x3f_1952_);
        crate::leanh::lean_dec_ref(v_ring_1951_);
        crate::leanh::lean_dec(v___f_1950_);
        crate::leanh::lean_dec(v_toBind_1949_);
        crate::leanh::lean_dec_ref(v_inst_1948_);
        crate::leanh::lean_dec_ref(v_inst_1947_);
        crate::leanh::lean_dec_ref(v_inst_1946_);
        crate::leanh::lean_dec(v_inst_1945_);
        v_val_1953_ = crate::leanh::lean_ctor_get(v_mulFn_x3f_1952_, 0);
        crate::leanh::lean_inc(v_val_1953_);
        crate::leanh::lean_dec_ref_known(v_mulFn_x3f_1952_, 1);
        v___x_1954_ =
            crate::leanh::lean_apply_2(v_toPure_1944_, crate::leanh::lean_box(0), v_val_1953_);
        return v___x_1954_;
    } else {
        let mut v_type_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1944_);
        v_type_1955_ = crate::leanh::lean_ctor_get(v_ring_1951_, 1);
        crate::leanh::lean_inc_ref_n(v_type_1955_, 3);
        v_u_1956_ = crate::leanh::lean_ctor_get(v_ring_1951_, 2);
        crate::leanh::lean_inc_n(v_u_1956_, 2);
        v_semiringInst_1957_ = crate::leanh::lean_ctor_get(v_ring_1951_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_1957_);
        crate::leanh::lean_dec_ref(v_ring_1951_);
        v___x_1958_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1;
        v___x_1959_ = crate::leanh::lean_box(0);
        v___x_1960_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1960_, 0, v_u_1956_);
        crate::leanh::lean_ctor_set(v___x_1960_, 1, v___x_1959_);
        crate::leanh::lean_inc_ref(v___x_1960_);
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
        v___x_1969_ = crate::leanh::lean_apply_4(
            v_toBind_1949_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1968_,
            v___f_1950_,
        );
        return v___x_1969_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
    mut v_inst_1970_: *mut crate::leanh::LeanObject,
    mut v_inst_1971_: *mut crate::leanh::LeanObject,
    mut v_inst_1972_: *mut crate::leanh::LeanObject,
    mut v_inst_1973_: *mut crate::leanh::LeanObject,
    mut v_inst_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1975_ = crate::leanh::lean_ctor_get(v_inst_1972_, 0);
    v_toBind_1976_ = crate::leanh::lean_ctor_get(v_inst_1972_, 1);
    crate::leanh::lean_inc_n(v_toBind_1976_, 3);
    v_getRing_1977_ = crate::leanh::lean_ctor_get(v_inst_1974_, 0);
    crate::leanh::lean_inc(v_getRing_1977_);
    v_modifyRing_1978_ = crate::leanh::lean_ctor_get(v_inst_1974_, 1);
    crate::leanh::lean_inc(v_modifyRing_1978_);
    crate::leanh::lean_dec_ref(v_inst_1974_);
    v_toPure_1979_ = crate::leanh::lean_ctor_get(v_toApplicative_1975_, 1);
    crate::leanh::lean_inc_n(v_toPure_1979_, 2);
    v___f_1980_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1980_, 0, v_toPure_1979_);
    crate::leanh::lean_closure_set(v___f_1980_, 1, v_modifyRing_1978_);
    crate::leanh::lean_closure_set(v___f_1980_, 2, v_toBind_1976_);
    v___f_1981_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1981_, 0, v_toPure_1979_);
    crate::leanh::lean_closure_set(v___f_1981_, 1, v_inst_1970_);
    crate::leanh::lean_closure_set(v___f_1981_, 2, v_inst_1971_);
    crate::leanh::lean_closure_set(v___f_1981_, 3, v_inst_1972_);
    crate::leanh::lean_closure_set(v___f_1981_, 4, v_inst_1973_);
    crate::leanh::lean_closure_set(v___f_1981_, 5, v_toBind_1976_);
    crate::leanh::lean_closure_set(v___f_1981_, 6, v___f_1980_);
    v___x_1982_ = crate::leanh::lean_apply_4(
        v_toBind_1976_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_1977_,
        v___f_1981_,
    );
    return v___x_1982_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn(
    mut v_m_1983_: *mut crate::leanh::LeanObject,
    mut v_inst_1984_: *mut crate::leanh::LeanObject,
    mut v_inst_1985_: *mut crate::leanh::LeanObject,
    mut v_inst_1986_: *mut crate::leanh::LeanObject,
    mut v_inst_1987_: *mut crate::leanh::LeanObject,
    mut v_inst_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_negFn_1990_: *mut crate::leanh::LeanObject,
    mut v_s_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_unused_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1992_ = crate::leanh::lean_ctor_get(v_s_1991_, 0);
                v_type_1993_ = crate::leanh::lean_ctor_get(v_s_1991_, 1);
                v_u_1994_ = crate::leanh::lean_ctor_get(v_s_1991_, 2);
                v_ringInst_1995_ = crate::leanh::lean_ctor_get(v_s_1991_, 3);
                v_semiringInst_1996_ = crate::leanh::lean_ctor_get(v_s_1991_, 4);
                v_charInst_x3f_1997_ = crate::leanh::lean_ctor_get(v_s_1991_, 5);
                v_addFn_x3f_1998_ = crate::leanh::lean_ctor_get(v_s_1991_, 6);
                v_mulFn_x3f_1999_ = crate::leanh::lean_ctor_get(v_s_1991_, 7);
                v_subFn_x3f_2000_ = crate::leanh::lean_ctor_get(v_s_1991_, 8);
                v_powFn_x3f_2001_ = crate::leanh::lean_ctor_get(v_s_1991_, 10);
                v_intCastFn_x3f_2002_ = crate::leanh::lean_ctor_get(v_s_1991_, 11);
                v_natCastFn_x3f_2003_ = crate::leanh::lean_ctor_get(v_s_1991_, 12);
                v_one_x3f_2004_ = crate::leanh::lean_ctor_get(v_s_1991_, 13);
                v_vars_2005_ = crate::leanh::lean_ctor_get(v_s_1991_, 14);
                v_varMap_2006_ = crate::leanh::lean_ctor_get(v_s_1991_, 15);
                v_denote_2007_ = crate::leanh::lean_ctor_get(v_s_1991_, 16);
                v_isSharedCheck_2015_ = (!crate::leanh::lean_is_exclusive(v_s_1991_)) as u8;
                if v_isSharedCheck_2015_ == 0 {
                    v_unused_2016_ = crate::leanh::lean_ctor_get(v_s_1991_, 9);
                    crate::leanh::lean_dec(v_unused_2016_);
                    v___x_2009_ = v_s_1991_;
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2007_);
                    crate::leanh::lean_inc(v_varMap_2006_);
                    crate::leanh::lean_inc(v_vars_2005_);
                    crate::leanh::lean_inc(v_one_x3f_2004_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2003_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2002_);
                    crate::leanh::lean_inc(v_powFn_x3f_2001_);
                    crate::leanh::lean_inc(v_subFn_x3f_2000_);
                    crate::leanh::lean_inc(v_mulFn_x3f_1999_);
                    crate::leanh::lean_inc(v_addFn_x3f_1998_);
                    crate::leanh::lean_inc(v_charInst_x3f_1997_);
                    crate::leanh::lean_inc(v_semiringInst_1996_);
                    crate::leanh::lean_inc(v_ringInst_1995_);
                    crate::leanh::lean_inc(v_u_1994_);
                    crate::leanh::lean_inc(v_type_1993_);
                    crate::leanh::lean_inc(v_id_1992_);
                    crate::leanh::lean_dec(v_s_1991_);
                    v___x_2009_ = crate::leanh::lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2011_, 0, v_negFn_1990_);
                if v_isShared_2010_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2009_, 9, v___x_2011_);
                    v___x_2013_ = v___x_2009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_id_1992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_type_1993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_u_1994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_ringInst_1995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_semiringInst_1996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_charInst_x3f_1997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_addFn_x3f_1998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_mulFn_x3f_1999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_subFn_x3f_2000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 9, v___x_2011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 10, v_powFn_x3f_2001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 11, v_intCastFn_x3f_2002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 12, v_natCastFn_x3f_2003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 13, v_one_x3f_2004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 14, v_vars_2005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 15, v_varMap_2006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 16, v_denote_2007_);
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
    mut v_toPure_2017_: *mut crate::leanh::LeanObject,
    mut v_negFn_2018_: *mut crate::leanh::LeanObject,
    mut v_____r_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ =
        crate::leanh::lean_apply_2(v_toPure_2017_, crate::leanh::lean_box(0), v_negFn_2018_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2(
    mut v_toPure_2021_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2022_: *mut crate::leanh::LeanObject,
    mut v_toBind_2023_: *mut crate::leanh::LeanObject,
    mut v_negFn_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_negFn_2024_);
    v___f_2025_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2025_, 0, v_negFn_2024_);
    v___f_2026_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2026_, 0, v_toPure_2021_);
    crate::leanh::lean_closure_set(v___f_2026_, 1, v_negFn_2024_);
    v___x_2027_ = crate::leanh::lean_apply_1(v_modifyRing_2022_, v___f_2025_);
    v___x_2028_ = crate::leanh::lean_apply_4(
        v_toBind_2023_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2027_,
        v___f_2026_,
    );
    return v___x_2028_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(
    mut v_toPure_2042_: *mut crate::leanh::LeanObject,
    mut v_inst_2043_: *mut crate::leanh::LeanObject,
    mut v_inst_2044_: *mut crate::leanh::LeanObject,
    mut v_inst_2045_: *mut crate::leanh::LeanObject,
    mut v_inst_2046_: *mut crate::leanh::LeanObject,
    mut v_toBind_2047_: *mut crate::leanh::LeanObject,
    mut v___f_2048_: *mut crate::leanh::LeanObject,
    mut v_ring_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_negFn_x3f_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_negFn_x3f_2050_ = crate::leanh::lean_ctor_get(v_ring_2049_, 9);
    if crate::leanh::lean_obj_tag(v_negFn_x3f_2050_) == 1 {
        let mut v_val_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_negFn_x3f_2050_);
        crate::leanh::lean_dec_ref(v_ring_2049_);
        crate::leanh::lean_dec(v___f_2048_);
        crate::leanh::lean_dec(v_toBind_2047_);
        crate::leanh::lean_dec_ref(v_inst_2046_);
        crate::leanh::lean_dec_ref(v_inst_2045_);
        crate::leanh::lean_dec_ref(v_inst_2044_);
        crate::leanh::lean_dec(v_inst_2043_);
        v_val_2051_ = crate::leanh::lean_ctor_get(v_negFn_x3f_2050_, 0);
        crate::leanh::lean_inc(v_val_2051_);
        crate::leanh::lean_dec_ref_known(v_negFn_x3f_2050_, 1);
        v___x_2052_ =
            crate::leanh::lean_apply_2(v_toPure_2042_, crate::leanh::lean_box(0), v_val_2051_);
        return v___x_2052_;
    } else {
        let mut v_type_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ringInst_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2042_);
        v_type_2053_ = crate::leanh::lean_ctor_get(v_ring_2049_, 1);
        crate::leanh::lean_inc_ref_n(v_type_2053_, 2);
        v_u_2054_ = crate::leanh::lean_ctor_get(v_ring_2049_, 2);
        crate::leanh::lean_inc_n(v_u_2054_, 2);
        v_ringInst_2055_ = crate::leanh::lean_ctor_get(v_ring_2049_, 3);
        crate::leanh::lean_inc_ref(v_ringInst_2055_);
        crate::leanh::lean_dec_ref(v_ring_2049_);
        v___x_2056_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1;
        v___x_2057_ = crate::leanh::lean_box(0);
        v___x_2058_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2058_, 0, v_u_2054_);
        crate::leanh::lean_ctor_set(v___x_2058_, 1, v___x_2057_);
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
        v___x_2064_ = crate::leanh::lean_apply_4(
            v_toBind_2047_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2063_,
            v___f_2048_,
        );
        return v___x_2064_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
    mut v_inst_2065_: *mut crate::leanh::LeanObject,
    mut v_inst_2066_: *mut crate::leanh::LeanObject,
    mut v_inst_2067_: *mut crate::leanh::LeanObject,
    mut v_inst_2068_: *mut crate::leanh::LeanObject,
    mut v_inst_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2070_ = crate::leanh::lean_ctor_get(v_inst_2067_, 0);
    v_toBind_2071_ = crate::leanh::lean_ctor_get(v_inst_2067_, 1);
    crate::leanh::lean_inc_n(v_toBind_2071_, 3);
    v_getRing_2072_ = crate::leanh::lean_ctor_get(v_inst_2069_, 0);
    crate::leanh::lean_inc(v_getRing_2072_);
    v_modifyRing_2073_ = crate::leanh::lean_ctor_get(v_inst_2069_, 1);
    crate::leanh::lean_inc(v_modifyRing_2073_);
    crate::leanh::lean_dec_ref(v_inst_2069_);
    v_toPure_2074_ = crate::leanh::lean_ctor_get(v_toApplicative_2070_, 1);
    crate::leanh::lean_inc_n(v_toPure_2074_, 2);
    v___f_2075_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2075_, 0, v_toPure_2074_);
    crate::leanh::lean_closure_set(v___f_2075_, 1, v_modifyRing_2073_);
    crate::leanh::lean_closure_set(v___f_2075_, 2, v_toBind_2071_);
    v___f_2076_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2076_, 0, v_toPure_2074_);
    crate::leanh::lean_closure_set(v___f_2076_, 1, v_inst_2065_);
    crate::leanh::lean_closure_set(v___f_2076_, 2, v_inst_2066_);
    crate::leanh::lean_closure_set(v___f_2076_, 3, v_inst_2067_);
    crate::leanh::lean_closure_set(v___f_2076_, 4, v_inst_2068_);
    crate::leanh::lean_closure_set(v___f_2076_, 5, v_toBind_2071_);
    crate::leanh::lean_closure_set(v___f_2076_, 6, v___f_2075_);
    v___x_2077_ = crate::leanh::lean_apply_4(
        v_toBind_2071_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2072_,
        v___f_2076_,
    );
    return v___x_2077_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn(
    mut v_m_2078_: *mut crate::leanh::LeanObject,
    mut v_inst_2079_: *mut crate::leanh::LeanObject,
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
    mut v_inst_2081_: *mut crate::leanh::LeanObject,
    mut v_inst_2082_: *mut crate::leanh::LeanObject,
    mut v_inst_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_powFn_2085_: *mut crate::leanh::LeanObject,
    mut v_s_2086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2105_: u8 = 0;
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_unused_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2087_ = crate::leanh::lean_ctor_get(v_s_2086_, 0);
                v_type_2088_ = crate::leanh::lean_ctor_get(v_s_2086_, 1);
                v_u_2089_ = crate::leanh::lean_ctor_get(v_s_2086_, 2);
                v_ringInst_2090_ = crate::leanh::lean_ctor_get(v_s_2086_, 3);
                v_semiringInst_2091_ = crate::leanh::lean_ctor_get(v_s_2086_, 4);
                v_charInst_x3f_2092_ = crate::leanh::lean_ctor_get(v_s_2086_, 5);
                v_addFn_x3f_2093_ = crate::leanh::lean_ctor_get(v_s_2086_, 6);
                v_mulFn_x3f_2094_ = crate::leanh::lean_ctor_get(v_s_2086_, 7);
                v_subFn_x3f_2095_ = crate::leanh::lean_ctor_get(v_s_2086_, 8);
                v_negFn_x3f_2096_ = crate::leanh::lean_ctor_get(v_s_2086_, 9);
                v_intCastFn_x3f_2097_ = crate::leanh::lean_ctor_get(v_s_2086_, 11);
                v_natCastFn_x3f_2098_ = crate::leanh::lean_ctor_get(v_s_2086_, 12);
                v_one_x3f_2099_ = crate::leanh::lean_ctor_get(v_s_2086_, 13);
                v_vars_2100_ = crate::leanh::lean_ctor_get(v_s_2086_, 14);
                v_varMap_2101_ = crate::leanh::lean_ctor_get(v_s_2086_, 15);
                v_denote_2102_ = crate::leanh::lean_ctor_get(v_s_2086_, 16);
                v_isSharedCheck_2110_ = (!crate::leanh::lean_is_exclusive(v_s_2086_)) as u8;
                if v_isSharedCheck_2110_ == 0 {
                    v_unused_2111_ = crate::leanh::lean_ctor_get(v_s_2086_, 10);
                    crate::leanh::lean_dec(v_unused_2111_);
                    v___x_2104_ = v_s_2086_;
                    v_isShared_2105_ = v_isSharedCheck_2110_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2102_);
                    crate::leanh::lean_inc(v_varMap_2101_);
                    crate::leanh::lean_inc(v_vars_2100_);
                    crate::leanh::lean_inc(v_one_x3f_2099_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2098_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2097_);
                    crate::leanh::lean_inc(v_negFn_x3f_2096_);
                    crate::leanh::lean_inc(v_subFn_x3f_2095_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2094_);
                    crate::leanh::lean_inc(v_addFn_x3f_2093_);
                    crate::leanh::lean_inc(v_charInst_x3f_2092_);
                    crate::leanh::lean_inc(v_semiringInst_2091_);
                    crate::leanh::lean_inc(v_ringInst_2090_);
                    crate::leanh::lean_inc(v_u_2089_);
                    crate::leanh::lean_inc(v_type_2088_);
                    crate::leanh::lean_inc(v_id_2087_);
                    crate::leanh::lean_dec(v_s_2086_);
                    v___x_2104_ = crate::leanh::lean_box(0);
                    v_isShared_2105_ = v_isSharedCheck_2110_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2106_, 0, v_powFn_2085_);
                if v_isShared_2105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2104_, 10, v___x_2106_);
                    v___x_2108_ = v___x_2104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_id_2087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_type_2088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_u_2089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_ringInst_2090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_semiringInst_2091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 5, v_charInst_x3f_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 6, v_addFn_x3f_2093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 7, v_mulFn_x3f_2094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 8, v_subFn_x3f_2095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 9, v_negFn_x3f_2096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 10, v___x_2106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 11, v_intCastFn_x3f_2097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 12, v_natCastFn_x3f_2098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 13, v_one_x3f_2099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 14, v_vars_2100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 15, v_varMap_2101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 16, v_denote_2102_);
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
    mut v_toPure_2112_: *mut crate::leanh::LeanObject,
    mut v_powFn_2113_: *mut crate::leanh::LeanObject,
    mut v_____r_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ =
        crate::leanh::lean_apply_2(v_toPure_2112_, crate::leanh::lean_box(0), v_powFn_2113_);
    return v___x_2115_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(
    mut v_toPure_2116_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2117_: *mut crate::leanh::LeanObject,
    mut v_toBind_2118_: *mut crate::leanh::LeanObject,
    mut v_powFn_2119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_powFn_2119_);
    v___f_2120_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2120_, 0, v_powFn_2119_);
    v___f_2121_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2121_, 0, v_toPure_2116_);
    crate::leanh::lean_closure_set(v___f_2121_, 1, v_powFn_2119_);
    v___x_2122_ = crate::leanh::lean_apply_1(v_modifyRing_2117_, v___f_2120_);
    v___x_2123_ = crate::leanh::lean_apply_4(
        v_toBind_2118_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2122_,
        v___f_2121_,
    );
    return v___x_2123_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(
    mut v_toPure_2124_: *mut crate::leanh::LeanObject,
    mut v_inst_2125_: *mut crate::leanh::LeanObject,
    mut v_inst_2126_: *mut crate::leanh::LeanObject,
    mut v_inst_2127_: *mut crate::leanh::LeanObject,
    mut v_inst_2128_: *mut crate::leanh::LeanObject,
    mut v_toBind_2129_: *mut crate::leanh::LeanObject,
    mut v___f_2130_: *mut crate::leanh::LeanObject,
    mut v_ring_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_powFn_x3f_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_powFn_x3f_2132_ = crate::leanh::lean_ctor_get(v_ring_2131_, 10);
    if crate::leanh::lean_obj_tag(v_powFn_x3f_2132_) == 1 {
        let mut v_val_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_powFn_x3f_2132_);
        crate::leanh::lean_dec_ref(v_ring_2131_);
        crate::leanh::lean_dec(v___f_2130_);
        crate::leanh::lean_dec(v_toBind_2129_);
        crate::leanh::lean_dec_ref(v_inst_2128_);
        crate::leanh::lean_dec_ref(v_inst_2127_);
        crate::leanh::lean_dec_ref(v_inst_2126_);
        crate::leanh::lean_dec(v_inst_2125_);
        v_val_2133_ = crate::leanh::lean_ctor_get(v_powFn_x3f_2132_, 0);
        crate::leanh::lean_inc(v_val_2133_);
        crate::leanh::lean_dec_ref_known(v_powFn_x3f_2132_, 1);
        v___x_2134_ =
            crate::leanh::lean_apply_2(v_toPure_2124_, crate::leanh::lean_box(0), v_val_2133_);
        return v___x_2134_;
    } else {
        let mut v_type_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2124_);
        v_type_2135_ = crate::leanh::lean_ctor_get(v_ring_2131_, 1);
        crate::leanh::lean_inc_ref(v_type_2135_);
        v_u_2136_ = crate::leanh::lean_ctor_get(v_ring_2131_, 2);
        crate::leanh::lean_inc(v_u_2136_);
        v_semiringInst_2137_ = crate::leanh::lean_ctor_get(v_ring_2131_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_2137_);
        crate::leanh::lean_dec_ref(v_ring_2131_);
        v___x_2138_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
            v_inst_2125_,
            v_inst_2126_,
            v_inst_2127_,
            v_inst_2128_,
            v_u_2136_,
            v_type_2135_,
            v_semiringInst_2137_,
        );
        v___x_2139_ = crate::leanh::lean_apply_4(
            v_toBind_2129_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2138_,
            v___f_2130_,
        );
        return v___x_2139_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
    mut v_inst_2140_: *mut crate::leanh::LeanObject,
    mut v_inst_2141_: *mut crate::leanh::LeanObject,
    mut v_inst_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_inst_2144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2145_ = crate::leanh::lean_ctor_get(v_inst_2142_, 0);
    v_toBind_2146_ = crate::leanh::lean_ctor_get(v_inst_2142_, 1);
    crate::leanh::lean_inc_n(v_toBind_2146_, 3);
    v_getRing_2147_ = crate::leanh::lean_ctor_get(v_inst_2144_, 0);
    crate::leanh::lean_inc(v_getRing_2147_);
    v_modifyRing_2148_ = crate::leanh::lean_ctor_get(v_inst_2144_, 1);
    crate::leanh::lean_inc(v_modifyRing_2148_);
    crate::leanh::lean_dec_ref(v_inst_2144_);
    v_toPure_2149_ = crate::leanh::lean_ctor_get(v_toApplicative_2145_, 1);
    crate::leanh::lean_inc_n(v_toPure_2149_, 2);
    v___f_2150_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2150_, 0, v_toPure_2149_);
    crate::leanh::lean_closure_set(v___f_2150_, 1, v_modifyRing_2148_);
    crate::leanh::lean_closure_set(v___f_2150_, 2, v_toBind_2146_);
    v___f_2151_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2151_, 0, v_toPure_2149_);
    crate::leanh::lean_closure_set(v___f_2151_, 1, v_inst_2140_);
    crate::leanh::lean_closure_set(v___f_2151_, 2, v_inst_2141_);
    crate::leanh::lean_closure_set(v___f_2151_, 3, v_inst_2142_);
    crate::leanh::lean_closure_set(v___f_2151_, 4, v_inst_2143_);
    crate::leanh::lean_closure_set(v___f_2151_, 5, v_toBind_2146_);
    crate::leanh::lean_closure_set(v___f_2151_, 6, v___f_2150_);
    v___x_2152_ = crate::leanh::lean_apply_4(
        v_toBind_2146_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2147_,
        v___f_2151_,
    );
    return v___x_2152_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn(
    mut v_m_2153_: *mut crate::leanh::LeanObject,
    mut v_inst_2154_: *mut crate::leanh::LeanObject,
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
    mut v_inst_2156_: *mut crate::leanh::LeanObject,
    mut v_inst_2157_: *mut crate::leanh::LeanObject,
    mut v_inst_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_intCastFn_2160_: *mut crate::leanh::LeanObject,
    mut v_s_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_unused_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2162_ = crate::leanh::lean_ctor_get(v_s_2161_, 0);
                v_type_2163_ = crate::leanh::lean_ctor_get(v_s_2161_, 1);
                v_u_2164_ = crate::leanh::lean_ctor_get(v_s_2161_, 2);
                v_ringInst_2165_ = crate::leanh::lean_ctor_get(v_s_2161_, 3);
                v_semiringInst_2166_ = crate::leanh::lean_ctor_get(v_s_2161_, 4);
                v_charInst_x3f_2167_ = crate::leanh::lean_ctor_get(v_s_2161_, 5);
                v_addFn_x3f_2168_ = crate::leanh::lean_ctor_get(v_s_2161_, 6);
                v_mulFn_x3f_2169_ = crate::leanh::lean_ctor_get(v_s_2161_, 7);
                v_subFn_x3f_2170_ = crate::leanh::lean_ctor_get(v_s_2161_, 8);
                v_negFn_x3f_2171_ = crate::leanh::lean_ctor_get(v_s_2161_, 9);
                v_powFn_x3f_2172_ = crate::leanh::lean_ctor_get(v_s_2161_, 10);
                v_natCastFn_x3f_2173_ = crate::leanh::lean_ctor_get(v_s_2161_, 12);
                v_one_x3f_2174_ = crate::leanh::lean_ctor_get(v_s_2161_, 13);
                v_vars_2175_ = crate::leanh::lean_ctor_get(v_s_2161_, 14);
                v_varMap_2176_ = crate::leanh::lean_ctor_get(v_s_2161_, 15);
                v_denote_2177_ = crate::leanh::lean_ctor_get(v_s_2161_, 16);
                v_isSharedCheck_2185_ = (!crate::leanh::lean_is_exclusive(v_s_2161_)) as u8;
                if v_isSharedCheck_2185_ == 0 {
                    v_unused_2186_ = crate::leanh::lean_ctor_get(v_s_2161_, 11);
                    crate::leanh::lean_dec(v_unused_2186_);
                    v___x_2179_ = v_s_2161_;
                    v_isShared_2180_ = v_isSharedCheck_2185_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2177_);
                    crate::leanh::lean_inc(v_varMap_2176_);
                    crate::leanh::lean_inc(v_vars_2175_);
                    crate::leanh::lean_inc(v_one_x3f_2174_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2173_);
                    crate::leanh::lean_inc(v_powFn_x3f_2172_);
                    crate::leanh::lean_inc(v_negFn_x3f_2171_);
                    crate::leanh::lean_inc(v_subFn_x3f_2170_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2169_);
                    crate::leanh::lean_inc(v_addFn_x3f_2168_);
                    crate::leanh::lean_inc(v_charInst_x3f_2167_);
                    crate::leanh::lean_inc(v_semiringInst_2166_);
                    crate::leanh::lean_inc(v_ringInst_2165_);
                    crate::leanh::lean_inc(v_u_2164_);
                    crate::leanh::lean_inc(v_type_2163_);
                    crate::leanh::lean_inc(v_id_2162_);
                    crate::leanh::lean_dec(v_s_2161_);
                    v___x_2179_ = crate::leanh::lean_box(0);
                    v_isShared_2180_ = v_isSharedCheck_2185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2181_, 0, v_intCastFn_2160_);
                if v_isShared_2180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2179_, 11, v___x_2181_);
                    v___x_2183_ = v___x_2179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_id_2162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_type_2163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_u_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 3, v_ringInst_2165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_semiringInst_2166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 5, v_charInst_x3f_2167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 6, v_addFn_x3f_2168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 7, v_mulFn_x3f_2169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 8, v_subFn_x3f_2170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 9, v_negFn_x3f_2171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 10, v_powFn_x3f_2172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 11, v___x_2181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 12, v_natCastFn_x3f_2173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 13, v_one_x3f_2174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 14, v_vars_2175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 15, v_varMap_2176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 16, v_denote_2177_);
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
    mut v_toPure_2187_: *mut crate::leanh::LeanObject,
    mut v_intCastFn_2188_: *mut crate::leanh::LeanObject,
    mut v_____r_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ =
        crate::leanh::lean_apply_2(v_toPure_2187_, crate::leanh::lean_box(0), v_intCastFn_2188_);
    return v___x_2190_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2(
    mut v_toPure_2191_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2192_: *mut crate::leanh::LeanObject,
    mut v_toBind_2193_: *mut crate::leanh::LeanObject,
    mut v_intCastFn_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_intCastFn_2194_);
    v___f_2195_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2195_, 0, v_intCastFn_2194_);
    v___f_2196_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2196_, 0, v_toPure_2191_);
    crate::leanh::lean_closure_set(v___f_2196_, 1, v_intCastFn_2194_);
    v___x_2197_ = crate::leanh::lean_apply_1(v_modifyRing_2192_, v___f_2195_);
    v___x_2198_ = crate::leanh::lean_apply_4(
        v_toBind_2193_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2197_,
        v___f_2196_,
    );
    return v___x_2198_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3(
    mut v___x_2199_: *mut crate::leanh::LeanObject,
    mut v___x_2200_: *mut crate::leanh::LeanObject,
    mut v___x_2201_: *mut crate::leanh::LeanObject,
    mut v_type_2202_: *mut crate::leanh::LeanObject,
    mut v_canonExpr_2203_: *mut crate::leanh::LeanObject,
    mut v_toBind_2204_: *mut crate::leanh::LeanObject,
    mut v___f_2205_: *mut crate::leanh::LeanObject,
    mut v_inst_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ = l_Lean_Name_mkStr2(v___x_2199_, v___x_2200_);
    v___x_2208_ = l_Lean_mkConst(v___x_2207_, v___x_2201_);
    v___x_2209_ = l_Lean_mkAppB(v___x_2208_, v_type_2202_, v_inst_2206_);
    v___x_2210_ = crate::leanh::lean_apply_1(v_canonExpr_2203_, v___x_2209_);
    v___x_2211_ = crate::leanh::lean_apply_4(
        v_toBind_2204_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2210_,
        v___f_2205_,
    );
    return v___x_2211_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7(
    mut v_toPure_2217_: *mut crate::leanh::LeanObject,
    mut v_inst_x27_2218_: *mut crate::leanh::LeanObject,
    mut v_toBind_2219_: *mut crate::leanh::LeanObject,
    mut v___f_2220_: *mut crate::leanh::LeanObject,
    mut v___f_2221_: *mut crate::leanh::LeanObject,
    mut v_inst_2222_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2223_) == 0 {
        let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_2222_);
        crate::leanh::lean_dec(v___f_2221_);
        v___x_2224_ =
            crate::leanh::lean_apply_2(v_toPure_2217_, crate::leanh::lean_box(0), v_inst_x27_2218_);
        v___x_2225_ = crate::leanh::lean_apply_4(
            v_toBind_2219_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2224_,
            v___f_2220_,
        );
        return v___x_2225_;
    } else {
        let mut v_val_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2220_);
        v_val_2226_ = crate::leanh::lean_ctor_get(v_____do__lift_2223_, 0);
        crate::leanh::lean_inc_n(v_val_2226_, 2);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2223_, 1);
        crate::leanh::lean_inc(v_toBind_2219_);
        v___f_2227_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_2227_, 0, v_toPure_2217_);
        crate::leanh::lean_closure_set(v___f_2227_, 1, v_val_2226_);
        crate::leanh::lean_closure_set(v___f_2227_, 2, v_toBind_2219_);
        crate::leanh::lean_closure_set(v___f_2227_, 3, v___f_2221_);
        v___x_2228_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2;
        v___x_2229_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        crate::leanh::lean_closure_set(v___x_2229_, 0, v___x_2228_);
        crate::leanh::lean_closure_set(v___x_2229_, 1, v_val_2226_);
        crate::leanh::lean_closure_set(v___x_2229_, 2, v_inst_x27_2218_);
        v___x_2230_ =
            crate::leanh::lean_apply_2(v_inst_2222_, crate::leanh::lean_box(0), v___x_2229_);
        v___x_2231_ = crate::leanh::lean_apply_4(
            v_toBind_2219_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2230_,
            v___f_2227_,
        );
        return v___x_2231_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(
    mut v_toPure_2241_: *mut crate::leanh::LeanObject,
    mut v_inst_2242_: *mut crate::leanh::LeanObject,
    mut v_toBind_2243_: *mut crate::leanh::LeanObject,
    mut v___f_2244_: *mut crate::leanh::LeanObject,
    mut v_inst_2245_: *mut crate::leanh::LeanObject,
    mut v_ring_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intCastFn_x3f_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instType_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_intCastFn_x3f_2247_ = crate::leanh::lean_ctor_get(v_ring_2246_, 11);
                if crate::leanh::lean_obj_tag(v_intCastFn_x3f_2247_) == 1 {
                    crate::leanh::lean_inc_ref(v_intCastFn_x3f_2247_);
                    crate::leanh::lean_dec_ref(v_ring_2246_);
                    crate::leanh::lean_dec(v_inst_2245_);
                    crate::leanh::lean_dec(v___f_2244_);
                    crate::leanh::lean_dec(v_toBind_2243_);
                    crate::leanh::lean_dec_ref(v_inst_2242_);
                    v_val_2248_ = crate::leanh::lean_ctor_get(v_intCastFn_x3f_2247_, 0);
                    crate::leanh::lean_inc(v_val_2248_);
                    crate::leanh::lean_dec_ref_known(v_intCastFn_x3f_2247_, 1);
                    v___x_2249_ = crate::leanh::lean_apply_2(
                        v_toPure_2241_,
                        crate::leanh::lean_box(0),
                        v_val_2248_,
                    );
                    return v___x_2249_;
                } else {
                    v_type_2250_ = crate::leanh::lean_ctor_get(v_ring_2246_, 1);
                    crate::leanh::lean_inc_ref(v_type_2250_);
                    v_u_2251_ = crate::leanh::lean_ctor_get(v_ring_2246_, 2);
                    crate::leanh::lean_inc(v_u_2251_);
                    v_ringInst_2252_ = crate::leanh::lean_ctor_get(v_ring_2246_, 3);
                    crate::leanh::lean_inc_ref(v_ringInst_2252_);
                    crate::leanh::lean_dec_ref(v_ring_2246_);
                    v_canonExpr_2253_ = crate::leanh::lean_ctor_get(v_inst_2242_, 0);
                    v_synthInstance_x3f_2254_ = crate::leanh::lean_ctor_get(v_inst_2242_, 1);
                    v_isSharedCheck_2275_ = (!crate::leanh::lean_is_exclusive(v_inst_2242_)) as u8;
                    if v_isSharedCheck_2275_ == 0 {
                        v___x_2256_ = v_inst_2242_;
                        v_isShared_2257_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_synthInstance_x3f_2254_);
                        crate::leanh::lean_inc(v_canonExpr_2253_);
                        crate::leanh::lean_dec(v_inst_2242_);
                        v___x_2256_ = crate::leanh::lean_box(0);
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
                v___x_2260_ = crate::leanh::lean_box(0);
                if v_isShared_2257_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2256_, 1);
                    crate::leanh::lean_ctor_set(v___x_2256_, 1, v___x_2260_);
                    crate::leanh::lean_ctor_set(v___x_2256_, 0, v_u_2251_);
                    v___x_2262_ = v___x_2256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_u_2251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2260_);
                    v___x_2262_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___x_2262_, 2);
                v___x_2263_ = l_Lean_mkConst(v___x_2259_, v___x_2262_);
                crate::leanh::lean_inc_ref_n(v_type_2250_, 2);
                v_inst_x27_2264_ = l_Lean_mkAppB(v___x_2263_, v_type_2250_, v_ringInst_2252_);
                v___x_2265_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2;
                crate::leanh::lean_inc_n(v_toBind_2243_, 2);
                v___f_2266_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3
                        as *mut core::ffi::c_void,
                    8,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_2266_, 0, v___x_2265_);
                crate::leanh::lean_closure_set(v___f_2266_, 1, v___x_2258_);
                crate::leanh::lean_closure_set(v___f_2266_, 2, v___x_2262_);
                crate::leanh::lean_closure_set(v___f_2266_, 3, v_type_2250_);
                crate::leanh::lean_closure_set(v___f_2266_, 4, v_canonExpr_2253_);
                crate::leanh::lean_closure_set(v___f_2266_, 5, v_toBind_2243_);
                crate::leanh::lean_closure_set(v___f_2266_, 6, v___f_2244_);
                v___f_2267_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2267_, 0, v___f_2266_);
                crate::leanh::lean_inc_ref(v___f_2267_);
                v___f_2268_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_2268_, 0, v_toPure_2241_);
                crate::leanh::lean_closure_set(v___f_2268_, 1, v_inst_x27_2264_);
                crate::leanh::lean_closure_set(v___f_2268_, 2, v_toBind_2243_);
                crate::leanh::lean_closure_set(v___f_2268_, 3, v___f_2267_);
                crate::leanh::lean_closure_set(v___f_2268_, 4, v___f_2267_);
                crate::leanh::lean_closure_set(v___f_2268_, 5, v_inst_2245_);
                v___x_2269_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3;
                v___x_2270_ = l_Lean_mkConst(v___x_2269_, v___x_2262_);
                v_instType_2271_ = l_Lean_Expr_app___override(v___x_2270_, v_type_2250_);
                v___x_2272_ =
                    crate::leanh::lean_apply_1(v_synthInstance_x3f_2254_, v_instType_2271_);
                v___x_2273_ = crate::leanh::lean_apply_4(
                    v_toBind_2243_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_2276_: *mut crate::leanh::LeanObject,
    mut v_inst_2277_: *mut crate::leanh::LeanObject,
    mut v_inst_2278_: *mut crate::leanh::LeanObject,
    mut v_inst_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2280_ = crate::leanh::lean_ctor_get(v_inst_2277_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2280_);
    v_toBind_2281_ = crate::leanh::lean_ctor_get(v_inst_2277_, 1);
    crate::leanh::lean_inc_n(v_toBind_2281_, 3);
    crate::leanh::lean_dec_ref(v_inst_2277_);
    v_getRing_2282_ = crate::leanh::lean_ctor_get(v_inst_2279_, 0);
    crate::leanh::lean_inc(v_getRing_2282_);
    v_modifyRing_2283_ = crate::leanh::lean_ctor_get(v_inst_2279_, 1);
    crate::leanh::lean_inc(v_modifyRing_2283_);
    crate::leanh::lean_dec_ref(v_inst_2279_);
    v_toPure_2284_ = crate::leanh::lean_ctor_get(v_toApplicative_2280_, 1);
    crate::leanh::lean_inc_n(v_toPure_2284_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2280_);
    v___f_2285_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2285_, 0, v_toPure_2284_);
    crate::leanh::lean_closure_set(v___f_2285_, 1, v_modifyRing_2283_);
    crate::leanh::lean_closure_set(v___f_2285_, 2, v_toBind_2281_);
    v___f_2286_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2286_, 0, v_toPure_2284_);
    crate::leanh::lean_closure_set(v___f_2286_, 1, v_inst_2278_);
    crate::leanh::lean_closure_set(v___f_2286_, 2, v_toBind_2281_);
    crate::leanh::lean_closure_set(v___f_2286_, 3, v___f_2285_);
    crate::leanh::lean_closure_set(v___f_2286_, 4, v_inst_2276_);
    v___x_2287_ = crate::leanh::lean_apply_4(
        v_toBind_2281_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2282_,
        v___f_2286_,
    );
    return v___x_2287_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(
    mut v_m_2288_: *mut crate::leanh::LeanObject,
    mut v_inst_2289_: *mut crate::leanh::LeanObject,
    mut v_inst_2290_: *mut crate::leanh::LeanObject,
    mut v_inst_2291_: *mut crate::leanh::LeanObject,
    mut v_inst_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(
        v_inst_2289_,
        v_inst_2290_,
        v_inst_2291_,
        v_inst_2292_,
    );
    return v___x_2293_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(
    mut v_natCastFn_2294_: *mut crate::leanh::LeanObject,
    mut v_s_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_unused_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2296_ = crate::leanh::lean_ctor_get(v_s_2295_, 0);
                v_type_2297_ = crate::leanh::lean_ctor_get(v_s_2295_, 1);
                v_u_2298_ = crate::leanh::lean_ctor_get(v_s_2295_, 2);
                v_ringInst_2299_ = crate::leanh::lean_ctor_get(v_s_2295_, 3);
                v_semiringInst_2300_ = crate::leanh::lean_ctor_get(v_s_2295_, 4);
                v_charInst_x3f_2301_ = crate::leanh::lean_ctor_get(v_s_2295_, 5);
                v_addFn_x3f_2302_ = crate::leanh::lean_ctor_get(v_s_2295_, 6);
                v_mulFn_x3f_2303_ = crate::leanh::lean_ctor_get(v_s_2295_, 7);
                v_subFn_x3f_2304_ = crate::leanh::lean_ctor_get(v_s_2295_, 8);
                v_negFn_x3f_2305_ = crate::leanh::lean_ctor_get(v_s_2295_, 9);
                v_powFn_x3f_2306_ = crate::leanh::lean_ctor_get(v_s_2295_, 10);
                v_intCastFn_x3f_2307_ = crate::leanh::lean_ctor_get(v_s_2295_, 11);
                v_one_x3f_2308_ = crate::leanh::lean_ctor_get(v_s_2295_, 13);
                v_vars_2309_ = crate::leanh::lean_ctor_get(v_s_2295_, 14);
                v_varMap_2310_ = crate::leanh::lean_ctor_get(v_s_2295_, 15);
                v_denote_2311_ = crate::leanh::lean_ctor_get(v_s_2295_, 16);
                v_isSharedCheck_2319_ = (!crate::leanh::lean_is_exclusive(v_s_2295_)) as u8;
                if v_isSharedCheck_2319_ == 0 {
                    v_unused_2320_ = crate::leanh::lean_ctor_get(v_s_2295_, 12);
                    crate::leanh::lean_dec(v_unused_2320_);
                    v___x_2313_ = v_s_2295_;
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2311_);
                    crate::leanh::lean_inc(v_varMap_2310_);
                    crate::leanh::lean_inc(v_vars_2309_);
                    crate::leanh::lean_inc(v_one_x3f_2308_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2307_);
                    crate::leanh::lean_inc(v_powFn_x3f_2306_);
                    crate::leanh::lean_inc(v_negFn_x3f_2305_);
                    crate::leanh::lean_inc(v_subFn_x3f_2304_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2303_);
                    crate::leanh::lean_inc(v_addFn_x3f_2302_);
                    crate::leanh::lean_inc(v_charInst_x3f_2301_);
                    crate::leanh::lean_inc(v_semiringInst_2300_);
                    crate::leanh::lean_inc(v_ringInst_2299_);
                    crate::leanh::lean_inc(v_u_2298_);
                    crate::leanh::lean_inc(v_type_2297_);
                    crate::leanh::lean_inc(v_id_2296_);
                    crate::leanh::lean_dec(v_s_2295_);
                    v___x_2313_ = crate::leanh::lean_box(0);
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2315_, 0, v_natCastFn_2294_);
                if v_isShared_2314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2313_, 12, v___x_2315_);
                    v___x_2317_ = v___x_2313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_id_2296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_type_2297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_u_2298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_ringInst_2299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_semiringInst_2300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 5, v_charInst_x3f_2301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 6, v_addFn_x3f_2302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 7, v_mulFn_x3f_2303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 8, v_subFn_x3f_2304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 9, v_negFn_x3f_2305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 10, v_powFn_x3f_2306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 11, v_intCastFn_x3f_2307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 12, v___x_2315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 13, v_one_x3f_2308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 14, v_vars_2309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 15, v_varMap_2310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 16, v_denote_2311_);
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
    mut v_toPure_2321_: *mut crate::leanh::LeanObject,
    mut v_natCastFn_2322_: *mut crate::leanh::LeanObject,
    mut v_____r_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2324_ =
        crate::leanh::lean_apply_2(v_toPure_2321_, crate::leanh::lean_box(0), v_natCastFn_2322_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(
    mut v_toPure_2325_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2326_: *mut crate::leanh::LeanObject,
    mut v_toBind_2327_: *mut crate::leanh::LeanObject,
    mut v_natCastFn_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_natCastFn_2328_);
    v___f_2329_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2329_, 0, v_natCastFn_2328_);
    v___f_2330_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2330_, 0, v_toPure_2325_);
    crate::leanh::lean_closure_set(v___f_2330_, 1, v_natCastFn_2328_);
    v___x_2331_ = crate::leanh::lean_apply_1(v_modifyRing_2326_, v___f_2329_);
    v___x_2332_ = crate::leanh::lean_apply_4(
        v_toBind_2327_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2331_,
        v___f_2330_,
    );
    return v___x_2332_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(
    mut v_toPure_2333_: *mut crate::leanh::LeanObject,
    mut v_inst_2334_: *mut crate::leanh::LeanObject,
    mut v_inst_2335_: *mut crate::leanh::LeanObject,
    mut v_inst_2336_: *mut crate::leanh::LeanObject,
    mut v_toBind_2337_: *mut crate::leanh::LeanObject,
    mut v___f_2338_: *mut crate::leanh::LeanObject,
    mut v_ring_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natCastFn_x3f_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_2340_ = crate::leanh::lean_ctor_get(v_ring_2339_, 12);
    if crate::leanh::lean_obj_tag(v_natCastFn_x3f_2340_) == 1 {
        let mut v_val_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_natCastFn_x3f_2340_);
        crate::leanh::lean_dec_ref(v_ring_2339_);
        crate::leanh::lean_dec(v___f_2338_);
        crate::leanh::lean_dec(v_toBind_2337_);
        crate::leanh::lean_dec_ref(v_inst_2336_);
        crate::leanh::lean_dec_ref(v_inst_2335_);
        crate::leanh::lean_dec(v_inst_2334_);
        v_val_2341_ = crate::leanh::lean_ctor_get(v_natCastFn_x3f_2340_, 0);
        crate::leanh::lean_inc(v_val_2341_);
        crate::leanh::lean_dec_ref_known(v_natCastFn_x3f_2340_, 1);
        v___x_2342_ =
            crate::leanh::lean_apply_2(v_toPure_2333_, crate::leanh::lean_box(0), v_val_2341_);
        return v___x_2342_;
    } else {
        let mut v_type_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2333_);
        v_type_2343_ = crate::leanh::lean_ctor_get(v_ring_2339_, 1);
        crate::leanh::lean_inc_ref(v_type_2343_);
        v_u_2344_ = crate::leanh::lean_ctor_get(v_ring_2339_, 2);
        crate::leanh::lean_inc(v_u_2344_);
        v_semiringInst_2345_ = crate::leanh::lean_ctor_get(v_ring_2339_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_2345_);
        crate::leanh::lean_dec_ref(v_ring_2339_);
        v___x_2346_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
            v_inst_2334_,
            v_inst_2335_,
            v_inst_2336_,
            v_u_2344_,
            v_type_2343_,
            v_semiringInst_2345_,
        );
        v___x_2347_ = crate::leanh::lean_apply_4(
            v_toBind_2337_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2346_,
            v___f_2338_,
        );
        return v___x_2347_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
    mut v_inst_2348_: *mut crate::leanh::LeanObject,
    mut v_inst_2349_: *mut crate::leanh::LeanObject,
    mut v_inst_2350_: *mut crate::leanh::LeanObject,
    mut v_inst_2351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2352_ = crate::leanh::lean_ctor_get(v_inst_2349_, 0);
    v_toBind_2353_ = crate::leanh::lean_ctor_get(v_inst_2349_, 1);
    crate::leanh::lean_inc_n(v_toBind_2353_, 3);
    v_getRing_2354_ = crate::leanh::lean_ctor_get(v_inst_2351_, 0);
    crate::leanh::lean_inc(v_getRing_2354_);
    v_modifyRing_2355_ = crate::leanh::lean_ctor_get(v_inst_2351_, 1);
    crate::leanh::lean_inc(v_modifyRing_2355_);
    crate::leanh::lean_dec_ref(v_inst_2351_);
    v_toPure_2356_ = crate::leanh::lean_ctor_get(v_toApplicative_2352_, 1);
    crate::leanh::lean_inc_n(v_toPure_2356_, 2);
    v___f_2357_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2357_, 0, v_toPure_2356_);
    crate::leanh::lean_closure_set(v___f_2357_, 1, v_modifyRing_2355_);
    crate::leanh::lean_closure_set(v___f_2357_, 2, v_toBind_2353_);
    v___f_2358_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2358_, 0, v_toPure_2356_);
    crate::leanh::lean_closure_set(v___f_2358_, 1, v_inst_2348_);
    crate::leanh::lean_closure_set(v___f_2358_, 2, v_inst_2349_);
    crate::leanh::lean_closure_set(v___f_2358_, 3, v_inst_2350_);
    crate::leanh::lean_closure_set(v___f_2358_, 4, v_toBind_2353_);
    crate::leanh::lean_closure_set(v___f_2358_, 5, v___f_2357_);
    v___x_2359_ = crate::leanh::lean_apply_4(
        v_toBind_2353_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2354_,
        v___f_2358_,
    );
    return v___x_2359_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(
    mut v_m_2360_: *mut crate::leanh::LeanObject,
    mut v_inst_2361_: *mut crate::leanh::LeanObject,
    mut v_inst_2362_: *mut crate::leanh::LeanObject,
    mut v_inst_2363_: *mut crate::leanh::LeanObject,
    mut v_inst_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2365_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
        v_inst_2361_,
        v_inst_2362_,
        v_inst_2363_,
        v_inst_2364_,
    );
    return v___x_2365_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = crate::leanh::lean_unsigned_to_nat(1);
    v_n_2367_ = l_Lean_mkRawNatLit(v___x_2366_);
    return v_n_2367_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(
    mut v_inst_2378_: *mut crate::leanh::LeanObject,
    mut v_u_2379_: *mut crate::leanh::LeanObject,
    mut v_type_2380_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonExpr_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v_n_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNatInst_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v_unused_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_canonExpr_2382_ = crate::leanh::lean_ctor_get(v_inst_2378_, 0);
                v_isSharedCheck_2398_ = (!crate::leanh::lean_is_exclusive(v_inst_2378_)) as u8;
                if v_isSharedCheck_2398_ == 0 {
                    v_unused_2399_ = crate::leanh::lean_ctor_get(v_inst_2378_, 1);
                    crate::leanh::lean_dec(v_unused_2399_);
                    v___x_2384_ = v_inst_2378_;
                    v_isShared_2385_ = v_isSharedCheck_2398_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canonExpr_2382_);
                    crate::leanh::lean_dec(v_inst_2378_);
                    v___x_2384_ = crate::leanh::lean_box(0);
                    v_isShared_2385_ = v_isSharedCheck_2398_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_n_2386_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
                v___x_2387_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2;
                v___x_2388_ = crate::leanh::lean_box(0);
                if v_isShared_2385_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2384_, 1);
                    crate::leanh::lean_ctor_set(v___x_2384_, 1, v___x_2388_);
                    crate::leanh::lean_ctor_set(v___x_2384_, 0, v_u_2379_);
                    v___x_2390_ = v___x_2384_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_u_2379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2388_);
                    v___x_2390_ = v_reuseFailAlloc_2397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_2390_);
                v___x_2391_ = l_Lean_mkConst(v___x_2387_, v___x_2390_);
                crate::leanh::lean_inc_ref(v_type_2380_);
                v_ofNatInst_2392_ =
                    l_Lean_mkApp3(v___x_2391_, v_type_2380_, v_semiringInst_2381_, v_n_2386_);
                v___x_2393_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4;
                v___x_2394_ = l_Lean_mkConst(v___x_2393_, v___x_2390_);
                v___x_2395_ =
                    l_Lean_mkApp3(v___x_2394_, v_type_2380_, v_n_2386_, v_ofNatInst_2392_);
                v___x_2396_ = crate::leanh::lean_apply_1(v_canonExpr_2382_, v___x_2395_);
                return v___x_2396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne(
    mut v_m_2400_: *mut crate::leanh::LeanObject,
    mut v_inst_2401_: *mut crate::leanh::LeanObject,
    mut v_u_2402_: *mut crate::leanh::LeanObject,
    mut v_type_2403_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2405_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_2401_, v_u_2402_, v_type_2403_, v_semiringInst_2404_);
    return v___x_2405_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0(
    mut v_one_2406_: *mut crate::leanh::LeanObject,
    mut v_s_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut v_unused_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2408_ = crate::leanh::lean_ctor_get(v_s_2407_, 0);
                v_type_2409_ = crate::leanh::lean_ctor_get(v_s_2407_, 1);
                v_u_2410_ = crate::leanh::lean_ctor_get(v_s_2407_, 2);
                v_ringInst_2411_ = crate::leanh::lean_ctor_get(v_s_2407_, 3);
                v_semiringInst_2412_ = crate::leanh::lean_ctor_get(v_s_2407_, 4);
                v_charInst_x3f_2413_ = crate::leanh::lean_ctor_get(v_s_2407_, 5);
                v_addFn_x3f_2414_ = crate::leanh::lean_ctor_get(v_s_2407_, 6);
                v_mulFn_x3f_2415_ = crate::leanh::lean_ctor_get(v_s_2407_, 7);
                v_subFn_x3f_2416_ = crate::leanh::lean_ctor_get(v_s_2407_, 8);
                v_negFn_x3f_2417_ = crate::leanh::lean_ctor_get(v_s_2407_, 9);
                v_powFn_x3f_2418_ = crate::leanh::lean_ctor_get(v_s_2407_, 10);
                v_intCastFn_x3f_2419_ = crate::leanh::lean_ctor_get(v_s_2407_, 11);
                v_natCastFn_x3f_2420_ = crate::leanh::lean_ctor_get(v_s_2407_, 12);
                v_vars_2421_ = crate::leanh::lean_ctor_get(v_s_2407_, 14);
                v_varMap_2422_ = crate::leanh::lean_ctor_get(v_s_2407_, 15);
                v_denote_2423_ = crate::leanh::lean_ctor_get(v_s_2407_, 16);
                v_isSharedCheck_2431_ = (!crate::leanh::lean_is_exclusive(v_s_2407_)) as u8;
                if v_isSharedCheck_2431_ == 0 {
                    v_unused_2432_ = crate::leanh::lean_ctor_get(v_s_2407_, 13);
                    crate::leanh::lean_dec(v_unused_2432_);
                    v___x_2425_ = v_s_2407_;
                    v_isShared_2426_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2423_);
                    crate::leanh::lean_inc(v_varMap_2422_);
                    crate::leanh::lean_inc(v_vars_2421_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2420_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2419_);
                    crate::leanh::lean_inc(v_powFn_x3f_2418_);
                    crate::leanh::lean_inc(v_negFn_x3f_2417_);
                    crate::leanh::lean_inc(v_subFn_x3f_2416_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2415_);
                    crate::leanh::lean_inc(v_addFn_x3f_2414_);
                    crate::leanh::lean_inc(v_charInst_x3f_2413_);
                    crate::leanh::lean_inc(v_semiringInst_2412_);
                    crate::leanh::lean_inc(v_ringInst_2411_);
                    crate::leanh::lean_inc(v_u_2410_);
                    crate::leanh::lean_inc(v_type_2409_);
                    crate::leanh::lean_inc(v_id_2408_);
                    crate::leanh::lean_dec(v_s_2407_);
                    v___x_2425_ = crate::leanh::lean_box(0);
                    v_isShared_2426_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2427_, 0, v_one_2406_);
                if v_isShared_2426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2425_, 13, v___x_2427_);
                    v___x_2429_ = v___x_2425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_id_2408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_type_2409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_u_2410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_ringInst_2411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 4, v_semiringInst_2412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 5, v_charInst_x3f_2413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 6, v_addFn_x3f_2414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 7, v_mulFn_x3f_2415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 8, v_subFn_x3f_2416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 9, v_negFn_x3f_2417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 10, v_powFn_x3f_2418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 11, v_intCastFn_x3f_2419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 12, v_natCastFn_x3f_2420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 13, v___x_2427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 14, v_vars_2421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 15, v_varMap_2422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 16, v_denote_2423_);
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
    mut v_toPure_2433_: *mut crate::leanh::LeanObject,
    mut v_one_2434_: *mut crate::leanh::LeanObject,
    mut v_____r_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ =
        crate::leanh::lean_apply_2(v_toPure_2433_, crate::leanh::lean_box(0), v_one_2434_);
    return v___x_2436_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(
    mut v_one_2437_: *mut crate::leanh::LeanObject,
    mut v_inst_2438_: *mut crate::leanh::LeanObject,
    mut v_toBind_2439_: *mut crate::leanh::LeanObject,
    mut v___f_2440_: *mut crate::leanh::LeanObject,
    mut v_____r_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2443_ = crate::leanh::lean_box(0);
    v___x_2444_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_internalize___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2444_, 0, v_one_2437_);
    crate::leanh::lean_closure_set(v___x_2444_, 1, v___x_2442_);
    crate::leanh::lean_closure_set(v___x_2444_, 2, v___x_2443_);
    v___x_2445_ = crate::leanh::lean_apply_2(v_inst_2438_, crate::leanh::lean_box(0), v___x_2444_);
    v___x_2446_ = crate::leanh::lean_apply_4(
        v_toBind_2439_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2445_,
        v___f_2440_,
    );
    return v___x_2446_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(
    mut v_toPure_2447_: *mut crate::leanh::LeanObject,
    mut v_inst_2448_: *mut crate::leanh::LeanObject,
    mut v_toBind_2449_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_2450_: *mut crate::leanh::LeanObject,
    mut v_one_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_one_2451_, 2);
    v___f_2452_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2452_, 0, v_one_2451_);
    v___f_2453_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2453_, 0, v_toPure_2447_);
    crate::leanh::lean_closure_set(v___f_2453_, 1, v_one_2451_);
    crate::leanh::lean_inc(v_toBind_2449_);
    v___f_2454_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2454_, 0, v_one_2451_);
    crate::leanh::lean_closure_set(v___f_2454_, 1, v_inst_2448_);
    crate::leanh::lean_closure_set(v___f_2454_, 2, v_toBind_2449_);
    crate::leanh::lean_closure_set(v___f_2454_, 3, v___f_2453_);
    v___x_2455_ = crate::leanh::lean_apply_1(v_modifyRing_2450_, v___f_2452_);
    v___x_2456_ = crate::leanh::lean_apply_4(
        v_toBind_2449_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2455_,
        v___f_2454_,
    );
    return v___x_2456_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(
    mut v_toPure_2457_: *mut crate::leanh::LeanObject,
    mut v_inst_2458_: *mut crate::leanh::LeanObject,
    mut v_toBind_2459_: *mut crate::leanh::LeanObject,
    mut v___f_2460_: *mut crate::leanh::LeanObject,
    mut v_ring_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_one_x3f_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_one_x3f_2462_ = crate::leanh::lean_ctor_get(v_ring_2461_, 13);
    if crate::leanh::lean_obj_tag(v_one_x3f_2462_) == 1 {
        let mut v_val_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_one_x3f_2462_);
        crate::leanh::lean_dec_ref(v_ring_2461_);
        crate::leanh::lean_dec(v___f_2460_);
        crate::leanh::lean_dec(v_toBind_2459_);
        crate::leanh::lean_dec_ref(v_inst_2458_);
        v_val_2463_ = crate::leanh::lean_ctor_get(v_one_x3f_2462_, 0);
        crate::leanh::lean_inc(v_val_2463_);
        crate::leanh::lean_dec_ref_known(v_one_x3f_2462_, 1);
        v___x_2464_ =
            crate::leanh::lean_apply_2(v_toPure_2457_, crate::leanh::lean_box(0), v_val_2463_);
        return v___x_2464_;
    } else {
        let mut v_type_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2457_);
        v_type_2465_ = crate::leanh::lean_ctor_get(v_ring_2461_, 1);
        crate::leanh::lean_inc_ref(v_type_2465_);
        v_u_2466_ = crate::leanh::lean_ctor_get(v_ring_2461_, 2);
        crate::leanh::lean_inc(v_u_2466_);
        v_semiringInst_2467_ = crate::leanh::lean_ctor_get(v_ring_2461_, 4);
        crate::leanh::lean_inc_ref(v_semiringInst_2467_);
        crate::leanh::lean_dec_ref(v_ring_2461_);
        v___x_2468_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_2458_, v_u_2466_, v_type_2465_, v_semiringInst_2467_);
        v___x_2469_ = crate::leanh::lean_apply_4(
            v_toBind_2459_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2468_,
            v___f_2460_,
        );
        return v___x_2469_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(
    mut v_inst_2470_: *mut crate::leanh::LeanObject,
    mut v_inst_2471_: *mut crate::leanh::LeanObject,
    mut v_inst_2472_: *mut crate::leanh::LeanObject,
    mut v_inst_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2474_ = crate::leanh::lean_ctor_get(v_inst_2470_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2474_);
    v_toBind_2475_ = crate::leanh::lean_ctor_get(v_inst_2470_, 1);
    crate::leanh::lean_inc_n(v_toBind_2475_, 3);
    crate::leanh::lean_dec_ref(v_inst_2470_);
    v_getRing_2476_ = crate::leanh::lean_ctor_get(v_inst_2472_, 0);
    crate::leanh::lean_inc(v_getRing_2476_);
    v_modifyRing_2477_ = crate::leanh::lean_ctor_get(v_inst_2472_, 1);
    crate::leanh::lean_inc(v_modifyRing_2477_);
    crate::leanh::lean_dec_ref(v_inst_2472_);
    v_toPure_2478_ = crate::leanh::lean_ctor_get(v_toApplicative_2474_, 1);
    crate::leanh::lean_inc_n(v_toPure_2478_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_2474_);
    v___f_2479_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2479_, 0, v_toPure_2478_);
    crate::leanh::lean_closure_set(v___f_2479_, 1, v_inst_2473_);
    crate::leanh::lean_closure_set(v___f_2479_, 2, v_toBind_2475_);
    crate::leanh::lean_closure_set(v___f_2479_, 3, v_modifyRing_2477_);
    v___f_2480_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2480_, 0, v_toPure_2478_);
    crate::leanh::lean_closure_set(v___f_2480_, 1, v_inst_2471_);
    crate::leanh::lean_closure_set(v___f_2480_, 2, v_toBind_2475_);
    crate::leanh::lean_closure_set(v___f_2480_, 3, v___f_2479_);
    v___x_2481_ = crate::leanh::lean_apply_4(
        v_toBind_2475_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_2476_,
        v___f_2480_,
    );
    return v___x_2481_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne(
    mut v_m_2482_: *mut crate::leanh::LeanObject,
    mut v_inst_2483_: *mut crate::leanh::LeanObject,
    mut v_inst_2484_: *mut crate::leanh::LeanObject,
    mut v_inst_2485_: *mut crate::leanh::LeanObject,
    mut v_inst_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(
        v_inst_2483_,
        v_inst_2484_,
        v_inst_2485_,
        v_inst_2486_,
    );
    return v___x_2487_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0(
    mut v_invFn_2488_: *mut crate::leanh::LeanObject,
    mut v_s_2489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2503_: u8 = 0;
    let mut v_invSet_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2507_: u8 = 0;
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v_unused_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2490_ = crate::leanh::lean_ctor_get(v_s_2489_, 0);
                v_semiringId_x3f_2491_ = crate::leanh::lean_ctor_get(v_s_2489_, 2);
                v_commSemiringInst_2492_ = crate::leanh::lean_ctor_get(v_s_2489_, 3);
                v_commRingInst_2493_ = crate::leanh::lean_ctor_get(v_s_2489_, 4);
                v_noZeroDivInst_x3f_2494_ = crate::leanh::lean_ctor_get(v_s_2489_, 5);
                v_fieldInst_x3f_2495_ = crate::leanh::lean_ctor_get(v_s_2489_, 6);
                v_powIdentityInst_x3f_2496_ = crate::leanh::lean_ctor_get(v_s_2489_, 7);
                v_denoteEntries_2497_ = crate::leanh::lean_ctor_get(v_s_2489_, 8);
                v_nextId_2498_ = crate::leanh::lean_ctor_get(v_s_2489_, 9);
                v_steps_2499_ = crate::leanh::lean_ctor_get(v_s_2489_, 10);
                v_queue_2500_ = crate::leanh::lean_ctor_get(v_s_2489_, 11);
                v_basis_2501_ = crate::leanh::lean_ctor_get(v_s_2489_, 12);
                v_diseqs_2502_ = crate::leanh::lean_ctor_get(v_s_2489_, 13);
                v_recheck_2503_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2489_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2504_ = crate::leanh::lean_ctor_get(v_s_2489_, 14);
                v_powIdentityVarCount_2505_ = crate::leanh::lean_ctor_get(v_s_2489_, 15);
                v_numEq0_x3f_2506_ = crate::leanh::lean_ctor_get(v_s_2489_, 16);
                v_numEq0Updated_2507_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2489_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2515_ = (!crate::leanh::lean_is_exclusive(v_s_2489_)) as u8;
                if v_isSharedCheck_2515_ == 0 {
                    v_unused_2516_ = crate::leanh::lean_ctor_get(v_s_2489_, 1);
                    crate::leanh::lean_dec(v_unused_2516_);
                    v___x_2509_ = v_s_2489_;
                    v_isShared_2510_ = v_isSharedCheck_2515_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2506_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2505_);
                    crate::leanh::lean_inc(v_invSet_2504_);
                    crate::leanh::lean_inc(v_diseqs_2502_);
                    crate::leanh::lean_inc(v_basis_2501_);
                    crate::leanh::lean_inc(v_queue_2500_);
                    crate::leanh::lean_inc(v_steps_2499_);
                    crate::leanh::lean_inc(v_nextId_2498_);
                    crate::leanh::lean_inc(v_denoteEntries_2497_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2496_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2495_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2494_);
                    crate::leanh::lean_inc(v_commRingInst_2493_);
                    crate::leanh::lean_inc(v_commSemiringInst_2492_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2491_);
                    crate::leanh::lean_inc(v_toRing_2490_);
                    crate::leanh::lean_dec(v_s_2489_);
                    v___x_2509_ = crate::leanh::lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2511_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2511_, 0, v_invFn_2488_);
                if v_isShared_2510_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2509_, 1, v___x_2511_);
                    v___x_2513_ = v___x_2509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_toRing_2490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_semiringId_x3f_2491_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        3,
                        v_commSemiringInst_2492_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_commRingInst_2493_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        5,
                        v_noZeroDivInst_x3f_2494_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 6, v_fieldInst_x3f_2495_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        7,
                        v_powIdentityInst_x3f_2496_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 8, v_denoteEntries_2497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 9, v_nextId_2498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 10, v_steps_2499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 11, v_queue_2500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 12, v_basis_2501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 13, v_diseqs_2502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 14, v_invSet_2504_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        15,
                        v_powIdentityVarCount_2505_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 16, v_numEq0_x3f_2506_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2514_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2503_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2514_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
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
    mut v_toPure_2517_: *mut crate::leanh::LeanObject,
    mut v_invFn_2518_: *mut crate::leanh::LeanObject,
    mut v_____r_2519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2520_ =
        crate::leanh::lean_apply_2(v_toPure_2517_, crate::leanh::lean_box(0), v_invFn_2518_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2(
    mut v_toPure_2521_: *mut crate::leanh::LeanObject,
    mut v_modifyCommRing_2522_: *mut crate::leanh::LeanObject,
    mut v_toBind_2523_: *mut crate::leanh::LeanObject,
    mut v_invFn_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_invFn_2524_);
    v___f_2525_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2525_, 0, v_invFn_2524_);
    v___f_2526_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2526_, 0, v_toPure_2521_);
    crate::leanh::lean_closure_set(v___f_2526_, 1, v_invFn_2524_);
    v___x_2527_ = crate::leanh::lean_apply_1(v_modifyCommRing_2522_, v___f_2525_);
    v___x_2528_ = crate::leanh::lean_apply_4(
        v_toBind_2523_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2527_,
        v___f_2526_,
    );
    return v___x_2528_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7;
    v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
    return v___x_2545_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(
    mut v_toPure_2546_: *mut crate::leanh::LeanObject,
    mut v_inst_2547_: *mut crate::leanh::LeanObject,
    mut v_inst_2548_: *mut crate::leanh::LeanObject,
    mut v_inst_2549_: *mut crate::leanh::LeanObject,
    mut v_inst_2550_: *mut crate::leanh::LeanObject,
    mut v_toBind_2551_: *mut crate::leanh::LeanObject,
    mut v___f_2552_: *mut crate::leanh::LeanObject,
    mut v_ring_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fieldInst_x3f_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fieldInst_x3f_2554_ = crate::leanh::lean_ctor_get(v_ring_2553_, 6);
    if crate::leanh::lean_obj_tag(v_fieldInst_x3f_2554_) == 1 {
        let mut v_invFn_x3f_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_fieldInst_x3f_2554_);
        v_invFn_x3f_2555_ = crate::leanh::lean_ctor_get(v_ring_2553_, 1);
        if crate::leanh::lean_obj_tag(v_invFn_x3f_2555_) == 1 {
            let mut v_val_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_invFn_x3f_2555_);
            crate::leanh::lean_dec_ref_known(v_fieldInst_x3f_2554_, 1);
            crate::leanh::lean_dec_ref(v_ring_2553_);
            crate::leanh::lean_dec(v___f_2552_);
            crate::leanh::lean_dec(v_toBind_2551_);
            crate::leanh::lean_dec_ref(v_inst_2550_);
            crate::leanh::lean_dec_ref(v_inst_2549_);
            crate::leanh::lean_dec_ref(v_inst_2548_);
            crate::leanh::lean_dec(v_inst_2547_);
            v_val_2556_ = crate::leanh::lean_ctor_get(v_invFn_x3f_2555_, 0);
            crate::leanh::lean_inc(v_val_2556_);
            crate::leanh::lean_dec_ref_known(v_invFn_x3f_2555_, 1);
            v___x_2557_ =
                crate::leanh::lean_apply_2(v_toPure_2546_, crate::leanh::lean_box(0), v_val_2556_);
            return v___x_2557_;
        } else {
            let mut v_toRing_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_u_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedInst_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_2546_);
            v_toRing_2558_ = crate::leanh::lean_ctor_get(v_ring_2553_, 0);
            crate::leanh::lean_inc_ref(v_toRing_2558_);
            crate::leanh::lean_dec_ref(v_ring_2553_);
            v_val_2559_ = crate::leanh::lean_ctor_get(v_fieldInst_x3f_2554_, 0);
            crate::leanh::lean_inc(v_val_2559_);
            crate::leanh::lean_dec_ref_known(v_fieldInst_x3f_2554_, 1);
            v_type_2560_ = crate::leanh::lean_ctor_get(v_toRing_2558_, 1);
            crate::leanh::lean_inc_ref_n(v_type_2560_, 2);
            v_u_2561_ = crate::leanh::lean_ctor_get(v_toRing_2558_, 2);
            crate::leanh::lean_inc_n(v_u_2561_, 2);
            crate::leanh::lean_dec_ref(v_toRing_2558_);
            v___x_2562_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2;
            v___x_2563_ = crate::leanh::lean_box(0);
            v___x_2564_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2564_, 0, v_u_2561_);
            crate::leanh::lean_ctor_set(v___x_2564_, 1, v___x_2563_);
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
            v___x_2570_ = crate::leanh::lean_apply_4(
                v_toBind_2551_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2569_,
                v___f_2552_,
            );
            return v___x_2570_;
        }
    } else {
        let mut v_toRing_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_2552_);
        crate::leanh::lean_dec(v_toBind_2551_);
        crate::leanh::lean_dec_ref(v_inst_2550_);
        crate::leanh::lean_dec(v_inst_2547_);
        crate::leanh::lean_dec(v_toPure_2546_);
        v_toRing_2571_ = crate::leanh::lean_ctor_get(v_ring_2553_, 0);
        crate::leanh::lean_inc_ref(v_toRing_2571_);
        crate::leanh::lean_dec_ref(v_ring_2553_);
        v_type_2572_ = crate::leanh::lean_ctor_get(v_toRing_2571_, 1);
        crate::leanh::lean_inc_ref(v_type_2572_);
        crate::leanh::lean_dec_ref(v_toRing_2571_);
        v___x_2573_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once
            ),
            _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8,
        );
        v___x_2574_ = l_Lean_indentExpr(v_type_2572_);
        v___x_2575_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2575_, 0, v___x_2573_);
        crate::leanh::lean_ctor_set(v___x_2575_, 1, v___x_2574_);
        v___x_2576_ = l_Lean_throwError___redArg(v_inst_2549_, v_inst_2548_, v___x_2575_);
        return v___x_2576_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(
    mut v_inst_2577_: *mut crate::leanh::LeanObject,
    mut v_inst_2578_: *mut crate::leanh::LeanObject,
    mut v_inst_2579_: *mut crate::leanh::LeanObject,
    mut v_inst_2580_: *mut crate::leanh::LeanObject,
    mut v_inst_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2582_ = crate::leanh::lean_ctor_get(v_inst_2579_, 0);
    v_toBind_2583_ = crate::leanh::lean_ctor_get(v_inst_2579_, 1);
    crate::leanh::lean_inc_n(v_toBind_2583_, 3);
    v_getCommRing_2584_ = crate::leanh::lean_ctor_get(v_inst_2581_, 0);
    crate::leanh::lean_inc(v_getCommRing_2584_);
    v_modifyCommRing_2585_ = crate::leanh::lean_ctor_get(v_inst_2581_, 1);
    crate::leanh::lean_inc(v_modifyCommRing_2585_);
    crate::leanh::lean_dec_ref(v_inst_2581_);
    v_toPure_2586_ = crate::leanh::lean_ctor_get(v_toApplicative_2582_, 1);
    crate::leanh::lean_inc_n(v_toPure_2586_, 2);
    v___f_2587_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2587_, 0, v_toPure_2586_);
    crate::leanh::lean_closure_set(v___f_2587_, 1, v_modifyCommRing_2585_);
    crate::leanh::lean_closure_set(v___f_2587_, 2, v_toBind_2583_);
    v___f_2588_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2588_, 0, v_toPure_2586_);
    crate::leanh::lean_closure_set(v___f_2588_, 1, v_inst_2577_);
    crate::leanh::lean_closure_set(v___f_2588_, 2, v_inst_2578_);
    crate::leanh::lean_closure_set(v___f_2588_, 3, v_inst_2579_);
    crate::leanh::lean_closure_set(v___f_2588_, 4, v_inst_2580_);
    crate::leanh::lean_closure_set(v___f_2588_, 5, v_toBind_2583_);
    crate::leanh::lean_closure_set(v___f_2588_, 6, v___f_2587_);
    v___x_2589_ = crate::leanh::lean_apply_4(
        v_toBind_2583_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCommRing_2584_,
        v___f_2588_,
    );
    return v___x_2589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn(
    mut v_m_2590_: *mut crate::leanh::LeanObject,
    mut v_inst_2591_: *mut crate::leanh::LeanObject,
    mut v_inst_2592_: *mut crate::leanh::LeanObject,
    mut v_inst_2593_: *mut crate::leanh::LeanObject,
    mut v_inst_2594_: *mut crate::leanh::LeanObject,
    mut v_inst_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
}
