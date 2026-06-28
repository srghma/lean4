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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value: LeanStringObject<64> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 64,
        m_capacity: 64,
        m_length: 63,
        m_data: [
            101, 114, 114, 111, 114, 32, 119, 104, 105, 108, 101, 32, 105, 110, 105, 116, 105, 97,
            108, 105, 122, 105, 110, 103, 32, 96, 103, 114, 105, 110, 100, 32, 114, 105, 110, 103,
            96, 32, 111, 112, 101, 114, 97, 116, 111, 114, 115, 58, 10, 105, 110, 115, 116, 97,
            110, 99, 101, 32, 102, 111, 114, 32, 96, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value: LeanStringObject<3> =
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
        m_data: [96, 32, 0],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value: LeanStringObject<50> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 50,
        m_capacity: 50,
        m_length: 49,
        m_data: [
            10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
            97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32,
            101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value: LeanStringObject<59> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 59,
        m_capacity: 59,
        m_length: 58,
        m_data: [
            10, 119, 104, 101, 110, 32, 111, 110, 108, 121, 32, 114, 101, 100, 117, 99, 105, 98,
            108, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 97, 110, 100,
            32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 97, 114, 101, 32, 114, 101, 100,
            117, 99, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value:
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
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value:
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
    m_data: [110, 112, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value
)
    as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut LeanObject,
        12050285396929189622 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value
        ) as *mut LeanObject,
        18388652353510661091 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value:
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
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value)
                as *mut LeanObject,
            12847922472053947547 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut LeanObject,
        12050285396929189622 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value)
            as *mut LeanObject,
        14765357657372582228 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value)
            as *mut LeanObject,
        5779414593499529281 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        9594062259507646949 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut LeanObject,
        12050285396929189622 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        5442360487226035463 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
        ) as *mut LeanObject,
        10393083817453678557 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
        ) as *mut LeanObject,
        10393083817453678557 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value
        ) as *mut LeanObject,
        10680564408669940870 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        10135981711945425184 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value:
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
    m_data: [82, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value:
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
    m_data: [116, 111, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        10806710915646349764 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value
        ) as *mut LeanObject,
        18169824201013588232 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value:
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
    m_data: [72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
        ) as *mut LeanObject,
        16856108565602861689 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value:
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
    m_data: [104, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
        ) as *mut LeanObject,
        16856108565602861689 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value
        ) as *mut LeanObject,
        4187025665268973031 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        18134279130838690737 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut LeanObject,
        12050285396929189622 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        7102027102192867304 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
        ) as *mut LeanObject,
        2929883540436775422 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
        ) as *mut LeanObject,
        2929883540436775422 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value
        ) as *mut LeanObject,
        1611444129324655608 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value:
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
    m_data: [116, 111, 78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        10806710915646349764 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        10040236838748678500 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        9626815015619986526 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        9626815015619986526 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value
        ) as *mut LeanObject,
        17185717442815859305 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value:
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
    m_data: [99, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value
        ) as *mut LeanObject,
        7009148538150066493 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value
        ) as *mut LeanObject,
        439118677539554485 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut LeanObject,
        10806710915646349764 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value
        ) as *mut LeanObject,
        14561037289535094017 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value
        ) as *mut LeanObject,
        4977321555018234431 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut LeanObject,9341924117480681831 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value:
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
    m_data: [70, 105, 101, 108, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value:
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
    m_data: [116, 111, 73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut LeanObject,
        13563742693681136756 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        8615353994042975301 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value
        ) as *mut LeanObject,
        7723290638220826725 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value:
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
    m_data: [73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
        ) as *mut LeanObject,
        1412621069384631438 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value:
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
    m_data: [105, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value
) as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
        ) as *mut LeanObject,
        1412621069384631438 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value
        ) as *mut LeanObject,
        10171450186735820607 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value:
    LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value
) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(
    mut v_msgData_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    v___x_1305_ = lean_st_ref_get(v___y_1303_);
    v_env_1306_ = lean_ctor_get(v___x_1305_, 0);
    lean_inc_ref(v_env_1306_);
    lean_dec(v___x_1305_);
    v___x_1307_ = lean_st_ref_get(v___y_1301_);
    v_mctx_1308_ = lean_ctor_get(v___x_1307_, 0);
    lean_inc_ref(v_mctx_1308_);
    lean_dec(v___x_1307_);
    v_lctx_1309_ = lean_ctor_get(v___y_1300_, 2);
    v_options_1310_ = lean_ctor_get(v___y_1302_, 2);
    lean_inc_ref(v_options_1310_);
    lean_inc_ref(v_lctx_1309_);
    v___x_1311_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1311_, 0, v_env_1306_);
    lean_ctor_set(v___x_1311_, 1, v_mctx_1308_);
    lean_ctor_set(v___x_1311_, 2, v_lctx_1309_);
    lean_ctor_set(v___x_1311_, 3, v_options_1310_);
    v___x_1312_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1312_, 0, v___x_1311_);
    lean_ctor_set(v___x_1312_, 1, v_msgData_1299_);
    v___x_1313_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1313_, 0, v___x_1312_);
    return v___x_1313_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(
    mut v_msgData_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1320_: *mut LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msgData_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
    lean_dec(v___y_1318_);
    lean_dec_ref(v___y_1317_);
    lean_dec(v___y_1316_);
    lean_dec_ref(v___y_1315_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(
    mut v_msg_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1327_ = lean_ctor_get(v___y_1324_, 5);
                v___x_1328_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msg_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
                v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
                v_isSharedCheck_1337_ = (!lean_is_exclusive(v___x_1328_)) as u8;
                if v_isSharedCheck_1337_ == 0 {
                    v___x_1331_ = v___x_1328_;
                    v_isShared_1332_ = v_isSharedCheck_1337_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1329_);
                    lean_dec(v___x_1328_);
                    v___x_1331_ = lean_box(0);
                    v_isShared_1332_ = v_isSharedCheck_1337_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1327_);
                v___x_1333_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1333_, 0, v_ref_1327_);
                lean_ctor_set(v___x_1333_, 1, v_a_1329_);
                if v_isShared_1332_ == 0 {
                    lean_ctor_set_tag(v___x_1331_, 1);
                    lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
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
    mut v_msg_1338_: *mut LeanObject,
    mut v___y_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
    mut v___y_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1344_: *mut LeanObject = core::ptr::null_mut();
    v_res_1344_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(
            v_msg_1338_,
            v___y_1339_,
            v___y_1340_,
            v___y_1341_,
            v___y_1342_,
        );
    lean_dec(v___y_1342_);
    lean_dec_ref(v___y_1341_);
    lean_dec(v___y_1340_);
    lean_dec_ref(v___y_1339_);
    return v_res_1344_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1() -> *mut LeanObject {
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0;
    v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
    return v___x_1347_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3() -> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    v___x_1349_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2;
    v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
    return v___x_1350_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5() -> *mut LeanObject {
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4;
    v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
    return v___x_1353_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7() -> *mut LeanObject {
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6;
    v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
    return v___x_1356_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkInst(
    mut v_declName_1357_: *mut LeanObject,
    mut v_inst_1358_: *mut LeanObject,
    mut v_inst_x27_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
    mut v_a_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_a_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_inst_x27_1359_);
                lean_inc_ref(v_inst_1358_);
                v___x_1365_ = l_Lean_Meta_isDefEqI(
                    v_inst_1358_,
                    v_inst_x27_1359_,
                    v_a_1360_,
                    v_a_1361_,
                    v_a_1362_,
                    v_a_1363_,
                );
                if lean_obj_tag(v___x_1365_) == 0 {
                    v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1389_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1368_ = v___x_1365_;
                        v_isShared_1369_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1366_);
                        lean_dec(v___x_1365_);
                        v___x_1368_ = lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inst_x27_1359_);
                    lean_dec_ref(v_inst_1358_);
                    lean_dec(v_declName_1357_);
                    v_a_1390_ = lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1397_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1397_ == 0 {
                        v___x_1392_ = v___x_1365_;
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1390_);
                        lean_dec(v___x_1365_);
                        v___x_1392_ = lean_box(0);
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1370_ = (lean_unbox(v_a_1366_) as u8);
                lean_dec(v_a_1366_);
                if v___x_1370_ == 0 {
                    lean_del_object(v___x_1368_);
                    v___x_1371_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1,
                    );
                    v___x_1372_ = l_Lean_MessageData_ofName(v_declName_1357_);
                    v___x_1373_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1373_, 0, v___x_1371_);
                    lean_ctor_set(v___x_1373_, 1, v___x_1372_);
                    v___x_1374_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3,
                    );
                    v___x_1375_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1375_, 0, v___x_1373_);
                    lean_ctor_set(v___x_1375_, 1, v___x_1374_);
                    v___x_1376_ = l_Lean_indentExpr(v_inst_1358_);
                    v___x_1377_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1377_, 0, v___x_1375_);
                    lean_ctor_set(v___x_1377_, 1, v___x_1376_);
                    v___x_1378_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5,
                    );
                    v___x_1379_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1379_, 0, v___x_1377_);
                    lean_ctor_set(v___x_1379_, 1, v___x_1378_);
                    v___x_1380_ = l_Lean_indentExpr(v_inst_x27_1359_);
                    v___x_1381_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1381_, 0, v___x_1379_);
                    lean_ctor_set(v___x_1381_, 1, v___x_1380_);
                    v___x_1382_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7,
                    );
                    v___x_1383_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1383_, 0, v___x_1381_);
                    lean_ctor_set(v___x_1383_, 1, v___x_1382_);
                    v___x_1384_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v___x_1383_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
                    return v___x_1384_;
                } else {
                    lean_dec_ref(v_inst_x27_1359_);
                    lean_dec_ref(v_inst_1358_);
                    lean_dec(v_declName_1357_);
                    v___x_1385_ = lean_box(0);
                    if v_isShared_1369_ == 0 {
                        lean_ctor_set(v___x_1368_, 0, v___x_1385_);
                        v___x_1387_ = v___x_1368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
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
                    v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
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
    mut v_declName_1398_: *mut LeanObject,
    mut v_inst_1399_: *mut LeanObject,
    mut v_inst_x27_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
    mut v_a_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
    mut v_a_1405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1406_: *mut LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
        v_declName_1398_,
        v_inst_1399_,
        v_inst_x27_1400_,
        v_a_1401_,
        v_a_1402_,
        v_a_1403_,
        v_a_1404_,
    );
    lean_dec(v_a_1404_);
    lean_dec_ref(v_a_1403_);
    lean_dec(v_a_1402_);
    lean_dec_ref(v_a_1401_);
    return v_res_1406_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(
    mut v_00_u03b1_1407_: *mut LeanObject,
    mut v_msg_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1415_: *mut LeanObject,
    mut v_msg_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1422_: *mut LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(
        v_00_u03b1_1415_,
        v_msg_1416_,
        v___y_1417_,
        v___y_1418_,
        v___y_1419_,
        v___y_1420_,
    );
    lean_dec(v___y_1420_);
    lean_dec_ref(v___y_1419_);
    lean_dec(v___y_1418_);
    lean_dec_ref(v___y_1417_);
    return v_res_1422_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(
    mut v_inst_1423_: *mut LeanObject,
    mut v_declName_1424_: *mut LeanObject,
    mut v___x_1425_: *mut LeanObject,
    mut v_type_1426_: *mut LeanObject,
    mut v_inst_1427_: *mut LeanObject,
    mut v_____r_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v_canonExpr_1429_ = lean_ctor_get(v_inst_1423_, 0);
    lean_inc(v_canonExpr_1429_);
    lean_dec_ref(v_inst_1423_);
    v___x_1430_ = l_Lean_mkConst(v_declName_1424_, v___x_1425_);
    v___x_1431_ = l_Lean_mkAppB(v___x_1430_, v_type_1426_, v_inst_1427_);
    v___x_1432_ = lean_apply_1(v_canonExpr_1429_, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(
    mut v_inst_1433_: *mut LeanObject,
    mut v_declName_1434_: *mut LeanObject,
    mut v___x_1435_: *mut LeanObject,
    mut v_type_1436_: *mut LeanObject,
    mut v_expectedInst_1437_: *mut LeanObject,
    mut v_inst_1438_: *mut LeanObject,
    mut v_toBind_1439_: *mut LeanObject,
    mut v_inst_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1440_);
    lean_inc(v_declName_1434_);
    v___f_1441_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1441_, 0, v_inst_1433_);
    lean_closure_set(v___f_1441_, 1, v_declName_1434_);
    lean_closure_set(v___f_1441_, 2, v___x_1435_);
    lean_closure_set(v___f_1441_, 3, v_type_1436_);
    lean_closure_set(v___f_1441_, 4, v_inst_1440_);
    v___x_1442_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1442_, 0, v_declName_1434_);
    lean_closure_set(v___x_1442_, 1, v_inst_1440_);
    lean_closure_set(v___x_1442_, 2, v_expectedInst_1437_);
    v___x_1443_ = lean_apply_2(v_inst_1438_, lean_box(0), v___x_1442_);
    v___x_1444_ = lean_apply_4(
        v_toBind_1439_,
        lean_box(0),
        lean_box(0),
        v___x_1443_,
        v___f_1441_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(
    mut v_inst_1445_: *mut LeanObject,
    mut v_inst_1446_: *mut LeanObject,
    mut v_inst_1447_: *mut LeanObject,
    mut v_inst_1448_: *mut LeanObject,
    mut v_type_1449_: *mut LeanObject,
    mut v_u_1450_: *mut LeanObject,
    mut v_instDeclName_1451_: *mut LeanObject,
    mut v_declName_1452_: *mut LeanObject,
    mut v_expectedInst_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1454_ = lean_ctor_get(v_inst_1447_, 1);
    lean_inc_n(v_toBind_1454_, 2);
    v___x_1455_ = lean_box(0);
    v___x_1456_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1456_, 0, v_u_1450_);
    lean_ctor_set(v___x_1456_, 1, v___x_1455_);
    lean_inc_ref(v_type_1449_);
    lean_inc_ref(v___x_1456_);
    lean_inc_ref(v_inst_1448_);
    v___f_1457_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1457_, 0, v_inst_1448_);
    lean_closure_set(v___f_1457_, 1, v_declName_1452_);
    lean_closure_set(v___f_1457_, 2, v___x_1456_);
    lean_closure_set(v___f_1457_, 3, v_type_1449_);
    lean_closure_set(v___f_1457_, 4, v_expectedInst_1453_);
    lean_closure_set(v___f_1457_, 5, v_inst_1445_);
    lean_closure_set(v___f_1457_, 6, v_toBind_1454_);
    v___x_1458_ = l_Lean_mkConst(v_instDeclName_1451_, v___x_1456_);
    v___x_1459_ = l_Lean_Expr_app___override(v___x_1458_, v_type_1449_);
    v___x_1460_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1447_,
        v_inst_1446_,
        v_inst_1448_,
        v___x_1459_,
    );
    v___x_1461_ = lean_apply_4(
        v_toBind_1454_,
        lean_box(0),
        lean_box(0),
        v___x_1460_,
        v___f_1457_,
    );
    return v___x_1461_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(
    mut v_m_1462_: *mut LeanObject,
    mut v_inst_1463_: *mut LeanObject,
    mut v_inst_1464_: *mut LeanObject,
    mut v_inst_1465_: *mut LeanObject,
    mut v_inst_1466_: *mut LeanObject,
    mut v_type_1467_: *mut LeanObject,
    mut v_u_1468_: *mut LeanObject,
    mut v_instDeclName_1469_: *mut LeanObject,
    mut v_declName_1470_: *mut LeanObject,
    mut v_expectedInst_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1473_: *mut LeanObject,
    mut v_declName_1474_: *mut LeanObject,
    mut v___x_1475_: *mut LeanObject,
    mut v_type_1476_: *mut LeanObject,
    mut v_inst_1477_: *mut LeanObject,
    mut v_____r_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    v_canonExpr_1479_ = lean_ctor_get(v_inst_1473_, 0);
    lean_inc(v_canonExpr_1479_);
    lean_dec_ref(v_inst_1473_);
    v___x_1480_ = l_Lean_mkConst(v_declName_1474_, v___x_1475_);
    lean_inc_ref_n(v_type_1476_, 2);
    v___x_1481_ = l_Lean_mkApp4(
        v___x_1480_,
        v_type_1476_,
        v_type_1476_,
        v_type_1476_,
        v_inst_1477_,
    );
    v___x_1482_ = lean_apply_1(v_canonExpr_1479_, v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(
    mut v_inst_1483_: *mut LeanObject,
    mut v_declName_1484_: *mut LeanObject,
    mut v___x_1485_: *mut LeanObject,
    mut v_type_1486_: *mut LeanObject,
    mut v_expectedInst_1487_: *mut LeanObject,
    mut v_inst_1488_: *mut LeanObject,
    mut v_toBind_1489_: *mut LeanObject,
    mut v_inst_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_1490_);
    lean_inc(v_declName_1484_);
    v___f_1491_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1491_, 0, v_inst_1483_);
    lean_closure_set(v___f_1491_, 1, v_declName_1484_);
    lean_closure_set(v___f_1491_, 2, v___x_1485_);
    lean_closure_set(v___f_1491_, 3, v_type_1486_);
    lean_closure_set(v___f_1491_, 4, v_inst_1490_);
    v___x_1492_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1492_, 0, v_declName_1484_);
    lean_closure_set(v___x_1492_, 1, v_inst_1490_);
    lean_closure_set(v___x_1492_, 2, v_expectedInst_1487_);
    v___x_1493_ = lean_apply_2(v_inst_1488_, lean_box(0), v___x_1492_);
    v___x_1494_ = lean_apply_4(
        v_toBind_1489_,
        lean_box(0),
        lean_box(0),
        v___x_1493_,
        v___f_1491_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
    mut v_inst_1495_: *mut LeanObject,
    mut v_inst_1496_: *mut LeanObject,
    mut v_inst_1497_: *mut LeanObject,
    mut v_inst_1498_: *mut LeanObject,
    mut v_type_1499_: *mut LeanObject,
    mut v_u_1500_: *mut LeanObject,
    mut v_instDeclName_1501_: *mut LeanObject,
    mut v_declName_1502_: *mut LeanObject,
    mut v_expectedInst_1503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1504_ = lean_ctor_get(v_inst_1497_, 1);
    lean_inc_n(v_toBind_1504_, 2);
    v___x_1505_ = lean_box(0);
    lean_inc_n(v_u_1500_, 2);
    v___x_1506_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1506_, 0, v_u_1500_);
    lean_ctor_set(v___x_1506_, 1, v___x_1505_);
    v___x_1507_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1507_, 0, v_u_1500_);
    lean_ctor_set(v___x_1507_, 1, v___x_1506_);
    v___x_1508_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1508_, 0, v_u_1500_);
    lean_ctor_set(v___x_1508_, 1, v___x_1507_);
    lean_inc_ref_n(v_type_1499_, 3);
    lean_inc_ref(v___x_1508_);
    lean_inc_ref(v_inst_1498_);
    v___f_1509_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1509_, 0, v_inst_1498_);
    lean_closure_set(v___f_1509_, 1, v_declName_1502_);
    lean_closure_set(v___f_1509_, 2, v___x_1508_);
    lean_closure_set(v___f_1509_, 3, v_type_1499_);
    lean_closure_set(v___f_1509_, 4, v_expectedInst_1503_);
    lean_closure_set(v___f_1509_, 5, v_inst_1495_);
    lean_closure_set(v___f_1509_, 6, v_toBind_1504_);
    v___x_1510_ = l_Lean_mkConst(v_instDeclName_1501_, v___x_1508_);
    v___x_1511_ = l_Lean_mkApp3(v___x_1510_, v_type_1499_, v_type_1499_, v_type_1499_);
    v___x_1512_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1497_,
        v_inst_1496_,
        v_inst_1498_,
        v___x_1511_,
    );
    v___x_1513_ = lean_apply_4(
        v_toBind_1504_,
        lean_box(0),
        lean_box(0),
        v___x_1512_,
        v___f_1509_,
    );
    return v___x_1513_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn(
    mut v_m_1514_: *mut LeanObject,
    mut v_inst_1515_: *mut LeanObject,
    mut v_inst_1516_: *mut LeanObject,
    mut v_inst_1517_: *mut LeanObject,
    mut v_inst_1518_: *mut LeanObject,
    mut v_type_1519_: *mut LeanObject,
    mut v_u_1520_: *mut LeanObject,
    mut v_instDeclName_1521_: *mut LeanObject,
    mut v_declName_1522_: *mut LeanObject,
    mut v_expectedInst_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1525_: *mut LeanObject,
    mut v___x_1526_: *mut LeanObject,
    mut v___x_1527_: *mut LeanObject,
    mut v_type_1528_: *mut LeanObject,
    mut v___x_1529_: *mut LeanObject,
    mut v_inst_1530_: *mut LeanObject,
    mut v_____r_1531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    v_canonExpr_1532_ = lean_ctor_get(v_inst_1525_, 0);
    lean_inc(v_canonExpr_1532_);
    lean_dec_ref(v_inst_1525_);
    v___x_1533_ = l_Lean_mkConst(v___x_1526_, v___x_1527_);
    lean_inc_ref(v_type_1528_);
    v___x_1534_ = l_Lean_mkApp4(
        v___x_1533_,
        v_type_1528_,
        v___x_1529_,
        v_type_1528_,
        v_inst_1530_,
    );
    v___x_1535_ = lean_apply_1(v_canonExpr_1532_, v___x_1534_);
    return v___x_1535_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(
    mut v___x_1546_: *mut LeanObject,
    mut v_type_1547_: *mut LeanObject,
    mut v_semiringInst_1548_: *mut LeanObject,
    mut v___x_1549_: *mut LeanObject,
    mut v_inst_1550_: *mut LeanObject,
    mut v___x_1551_: *mut LeanObject,
    mut v___x_1552_: *mut LeanObject,
    mut v_inst_1553_: *mut LeanObject,
    mut v_toBind_1554_: *mut LeanObject,
    mut v_inst_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    v___x_1556_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4;
    v___x_1557_ = l_Lean_mkConst(v___x_1556_, v___x_1546_);
    lean_inc_ref(v_type_1547_);
    v_inst_x27_1558_ = l_Lean_mkAppB(v___x_1557_, v_type_1547_, v_semiringInst_1548_);
    v___x_1559_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5;
    v___x_1560_ = l_Lean_Name_mkStr2(v___x_1549_, v___x_1559_);
    lean_inc_ref(v_inst_1555_);
    lean_inc(v___x_1560_);
    v___f_1561_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1561_, 0, v_inst_1550_);
    lean_closure_set(v___f_1561_, 1, v___x_1560_);
    lean_closure_set(v___f_1561_, 2, v___x_1551_);
    lean_closure_set(v___f_1561_, 3, v_type_1547_);
    lean_closure_set(v___f_1561_, 4, v___x_1552_);
    lean_closure_set(v___f_1561_, 5, v_inst_1555_);
    v___x_1562_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1562_, 0, v___x_1560_);
    lean_closure_set(v___x_1562_, 1, v_inst_1555_);
    lean_closure_set(v___x_1562_, 2, v_inst_x27_1558_);
    v___x_1563_ = lean_apply_2(v_inst_1553_, lean_box(0), v___x_1562_);
    v___x_1564_ = lean_apply_4(
        v_toBind_1554_,
        lean_box(0),
        lean_box(0),
        v___x_1563_,
        v___f_1561_,
    );
    return v___x_1564_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = lean_unsigned_to_nat(0);
    v___x_1569_ = l_Lean_Level_ofNat(v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
    mut v_inst_1570_: *mut LeanObject,
    mut v_inst_1571_: *mut LeanObject,
    mut v_inst_1572_: *mut LeanObject,
    mut v_inst_1573_: *mut LeanObject,
    mut v_u_1574_: *mut LeanObject,
    mut v_type_1575_: *mut LeanObject,
    mut v_semiringInst_1576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1577_ = lean_ctor_get(v_inst_1572_, 1);
    lean_inc_n(v_toBind_1577_, 2);
    v___x_1578_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0;
    v___x_1579_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1;
    v___x_1580_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2,
    );
    v___x_1581_ = lean_box(0);
    lean_inc(v_u_1574_);
    v___x_1582_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1582_, 0, v_u_1574_);
    lean_ctor_set(v___x_1582_, 1, v___x_1581_);
    lean_inc_ref(v___x_1582_);
    v___x_1583_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1583_, 0, v___x_1580_);
    lean_ctor_set(v___x_1583_, 1, v___x_1582_);
    v___x_1584_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1584_, 0, v_u_1574_);
    lean_ctor_set(v___x_1584_, 1, v___x_1583_);
    lean_inc_ref(v___x_1584_);
    v___x_1585_ = l_Lean_mkConst(v___x_1579_, v___x_1584_);
    v___x_1586_ = l_Lean_Nat_mkType;
    lean_inc_ref(v_inst_1573_);
    lean_inc_ref_n(v_type_1575_, 2);
    v___f_1587_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_1587_, 0, v___x_1582_);
    lean_closure_set(v___f_1587_, 1, v_type_1575_);
    lean_closure_set(v___f_1587_, 2, v_semiringInst_1576_);
    lean_closure_set(v___f_1587_, 3, v___x_1578_);
    lean_closure_set(v___f_1587_, 4, v_inst_1573_);
    lean_closure_set(v___f_1587_, 5, v___x_1584_);
    lean_closure_set(v___f_1587_, 6, v___x_1586_);
    lean_closure_set(v___f_1587_, 7, v_inst_1570_);
    lean_closure_set(v___f_1587_, 8, v_toBind_1577_);
    v___x_1588_ = l_Lean_mkApp3(v___x_1585_, v_type_1575_, v___x_1586_, v_type_1575_);
    v___x_1589_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1572_,
        v_inst_1571_,
        v_inst_1573_,
        v___x_1588_,
    );
    v___x_1590_ = lean_apply_4(
        v_toBind_1577_,
        lean_box(0),
        lean_box(0),
        v___x_1589_,
        v___f_1587_,
    );
    return v___x_1590_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn(
    mut v_m_1591_: *mut LeanObject,
    mut v_inst_1592_: *mut LeanObject,
    mut v_inst_1593_: *mut LeanObject,
    mut v_inst_1594_: *mut LeanObject,
    mut v_inst_1595_: *mut LeanObject,
    mut v_u_1596_: *mut LeanObject,
    mut v_type_1597_: *mut LeanObject,
    mut v_semiringInst_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_1600_: *mut LeanObject,
    mut v___x_1601_: *mut LeanObject,
    mut v___x_1602_: *mut LeanObject,
    mut v_type_1603_: *mut LeanObject,
    mut v_canonExpr_1604_: *mut LeanObject,
    mut v_inst_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Name_mkStr2(v___x_1600_, v___x_1601_);
    v___x_1607_ = l_Lean_mkConst(v___x_1606_, v___x_1602_);
    v___x_1608_ = l_Lean_mkAppB(v___x_1607_, v_type_1603_, v_inst_1605_);
    v___x_1609_ = lean_apply_1(v_canonExpr_1604_, v___x_1608_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1(
    mut v___f_1610_: *mut LeanObject,
    mut v_inst_1611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    v___x_1612_ = lean_apply_1(v___f_1610_, v_inst_1611_);
    return v___x_1612_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3(
    mut v_toPure_1613_: *mut LeanObject,
    mut v_val_1614_: *mut LeanObject,
    mut v_toBind_1615_: *mut LeanObject,
    mut v___f_1616_: *mut LeanObject,
    mut v_____r_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = lean_apply_2(v_toPure_1613_, lean_box(0), v_val_1614_);
    v___x_1619_ = lean_apply_4(
        v_toBind_1615_,
        lean_box(0),
        lean_box(0),
        v___x_1618_,
        v___f_1616_,
    );
    return v___x_1619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2(
    mut v_toPure_1620_: *mut LeanObject,
    mut v_inst_x27_1621_: *mut LeanObject,
    mut v_toBind_1622_: *mut LeanObject,
    mut v___f_1623_: *mut LeanObject,
    mut v___f_1624_: *mut LeanObject,
    mut v___x_1625_: *mut LeanObject,
    mut v___x_1626_: *mut LeanObject,
    mut v_inst_1627_: *mut LeanObject,
    mut v_____do__lift_1628_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1628_) == 0 {
        let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_1627_);
        lean_dec_ref(v___x_1626_);
        lean_dec_ref(v___x_1625_);
        lean_dec(v___f_1624_);
        v___x_1629_ = lean_apply_2(v_toPure_1620_, lean_box(0), v_inst_x27_1621_);
        v___x_1630_ = lean_apply_4(
            v_toBind_1622_,
            lean_box(0),
            lean_box(0),
            v___x_1629_,
            v___f_1623_,
        );
        return v___x_1630_;
    } else {
        let mut v_val_1631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_1623_);
        v_val_1631_ = lean_ctor_get(v_____do__lift_1628_, 0);
        lean_inc_n(v_val_1631_, 2);
        lean_dec_ref_known(v_____do__lift_1628_, 1);
        lean_inc(v_toBind_1622_);
        v___f_1632_ = lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1632_, 0, v_toPure_1620_);
        lean_closure_set(v___f_1632_, 1, v_val_1631_);
        lean_closure_set(v___f_1632_, 2, v_toBind_1622_);
        lean_closure_set(v___f_1632_, 3, v___f_1624_);
        v___x_1633_ = l_Lean_Name_mkStr2(v___x_1625_, v___x_1626_);
        v___x_1634_ = lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        lean_closure_set(v___x_1634_, 0, v___x_1633_);
        lean_closure_set(v___x_1634_, 1, v_val_1631_);
        lean_closure_set(v___x_1634_, 2, v_inst_x27_1621_);
        v___x_1635_ = lean_apply_2(v_inst_1627_, lean_box(0), v___x_1634_);
        v___x_1636_ = lean_apply_4(
            v_toBind_1622_,
            lean_box(0),
            lean_box(0),
            v___x_1635_,
            v___f_1632_,
        );
        return v___x_1636_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
    mut v_inst_1646_: *mut LeanObject,
    mut v_inst_1647_: *mut LeanObject,
    mut v_inst_1648_: *mut LeanObject,
    mut v_u_1649_: *mut LeanObject,
    mut v_type_1650_: *mut LeanObject,
    mut v_semiringInst_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v_toPure_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instType_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1652_ = lean_ctor_get(v_inst_1647_, 0);
                lean_inc_ref(v_toApplicative_1652_);
                v_toBind_1653_ = lean_ctor_get(v_inst_1647_, 1);
                lean_inc(v_toBind_1653_);
                lean_dec_ref(v_inst_1647_);
                v_canonExpr_1654_ = lean_ctor_get(v_inst_1648_, 0);
                v_synthInstance_x3f_1655_ = lean_ctor_get(v_inst_1648_, 1);
                v_isSharedCheck_1677_ = (!lean_is_exclusive(v_inst_1648_)) as u8;
                if v_isSharedCheck_1677_ == 0 {
                    v___x_1657_ = v_inst_1648_;
                    v_isShared_1658_ = v_isSharedCheck_1677_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_synthInstance_x3f_1655_);
                    lean_inc(v_canonExpr_1654_);
                    lean_dec(v_inst_1648_);
                    v___x_1657_ = lean_box(0);
                    v_isShared_1658_ = v_isSharedCheck_1677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1659_ = lean_ctor_get(v_toApplicative_1652_, 1);
                lean_inc(v_toPure_1659_);
                lean_dec_ref(v_toApplicative_1652_);
                v___x_1660_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0;
                v___x_1661_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1;
                v___x_1662_ = lean_box(0);
                if v_isShared_1658_ == 0 {
                    lean_ctor_set_tag(v___x_1657_, 1);
                    lean_ctor_set(v___x_1657_, 1, v___x_1662_);
                    lean_ctor_set(v___x_1657_, 0, v_u_1649_);
                    v___x_1664_ = v___x_1657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_u_1649_);
                    lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1662_);
                    v___x_1664_ = v_reuseFailAlloc_1676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v___x_1664_, 2);
                v___x_1665_ = l_Lean_mkConst(v___x_1661_, v___x_1664_);
                lean_inc_ref_n(v_type_1650_, 2);
                v_inst_x27_1666_ = l_Lean_mkAppB(v___x_1665_, v_type_1650_, v_semiringInst_1651_);
                v___x_1667_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2;
                v___f_1668_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___f_1668_, 0, v___x_1667_);
                lean_closure_set(v___f_1668_, 1, v___x_1660_);
                lean_closure_set(v___f_1668_, 2, v___x_1664_);
                lean_closure_set(v___f_1668_, 3, v_type_1650_);
                lean_closure_set(v___f_1668_, 4, v_canonExpr_1654_);
                v___f_1669_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1669_, 0, v___f_1668_);
                v___x_1670_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3;
                v___x_1671_ = l_Lean_mkConst(v___x_1670_, v___x_1664_);
                v_instType_1672_ = l_Lean_Expr_app___override(v___x_1671_, v_type_1650_);
                v___x_1673_ = lean_apply_1(v_synthInstance_x3f_1655_, v_instType_1672_);
                lean_inc_ref(v___f_1669_);
                lean_inc(v_toBind_1653_);
                v___f_1674_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2
                        as *mut core::ffi::c_void,
                    9,
                    8,
                );
                lean_closure_set(v___f_1674_, 0, v_toPure_1659_);
                lean_closure_set(v___f_1674_, 1, v_inst_x27_1666_);
                lean_closure_set(v___f_1674_, 2, v_toBind_1653_);
                lean_closure_set(v___f_1674_, 3, v___f_1669_);
                lean_closure_set(v___f_1674_, 4, v___f_1669_);
                lean_closure_set(v___f_1674_, 5, v___x_1667_);
                lean_closure_set(v___f_1674_, 6, v___x_1660_);
                lean_closure_set(v___f_1674_, 7, v_inst_1646_);
                v___x_1675_ = lean_apply_4(
                    v_toBind_1653_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1678_: *mut LeanObject,
    mut v_inst_1679_: *mut LeanObject,
    mut v_inst_1680_: *mut LeanObject,
    mut v_inst_1681_: *mut LeanObject,
    mut v_u_1682_: *mut LeanObject,
    mut v_type_1683_: *mut LeanObject,
    mut v_semiringInst_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_addFn_1686_: *mut LeanObject,
    mut v_s_1687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v_unused_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1688_ = lean_ctor_get(v_s_1687_, 0);
                v_type_1689_ = lean_ctor_get(v_s_1687_, 1);
                v_u_1690_ = lean_ctor_get(v_s_1687_, 2);
                v_ringInst_1691_ = lean_ctor_get(v_s_1687_, 3);
                v_semiringInst_1692_ = lean_ctor_get(v_s_1687_, 4);
                v_charInst_x3f_1693_ = lean_ctor_get(v_s_1687_, 5);
                v_mulFn_x3f_1694_ = lean_ctor_get(v_s_1687_, 7);
                v_subFn_x3f_1695_ = lean_ctor_get(v_s_1687_, 8);
                v_negFn_x3f_1696_ = lean_ctor_get(v_s_1687_, 9);
                v_powFn_x3f_1697_ = lean_ctor_get(v_s_1687_, 10);
                v_intCastFn_x3f_1698_ = lean_ctor_get(v_s_1687_, 11);
                v_natCastFn_x3f_1699_ = lean_ctor_get(v_s_1687_, 12);
                v_one_x3f_1700_ = lean_ctor_get(v_s_1687_, 13);
                v_vars_1701_ = lean_ctor_get(v_s_1687_, 14);
                v_varMap_1702_ = lean_ctor_get(v_s_1687_, 15);
                v_denote_1703_ = lean_ctor_get(v_s_1687_, 16);
                v_isSharedCheck_1711_ = (!lean_is_exclusive(v_s_1687_)) as u8;
                if v_isSharedCheck_1711_ == 0 {
                    v_unused_1712_ = lean_ctor_get(v_s_1687_, 6);
                    lean_dec(v_unused_1712_);
                    v___x_1705_ = v_s_1687_;
                    v_isShared_1706_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_1703_);
                    lean_inc(v_varMap_1702_);
                    lean_inc(v_vars_1701_);
                    lean_inc(v_one_x3f_1700_);
                    lean_inc(v_natCastFn_x3f_1699_);
                    lean_inc(v_intCastFn_x3f_1698_);
                    lean_inc(v_powFn_x3f_1697_);
                    lean_inc(v_negFn_x3f_1696_);
                    lean_inc(v_subFn_x3f_1695_);
                    lean_inc(v_mulFn_x3f_1694_);
                    lean_inc(v_charInst_x3f_1693_);
                    lean_inc(v_semiringInst_1692_);
                    lean_inc(v_ringInst_1691_);
                    lean_inc(v_u_1690_);
                    lean_inc(v_type_1689_);
                    lean_inc(v_id_1688_);
                    lean_dec(v_s_1687_);
                    v___x_1705_ = lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1707_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1707_, 0, v_addFn_1686_);
                if v_isShared_1706_ == 0 {
                    lean_ctor_set(v___x_1705_, 6, v___x_1707_);
                    v___x_1709_ = v___x_1705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_id_1688_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_type_1689_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_u_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_ringInst_1691_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_semiringInst_1692_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 5, v_charInst_x3f_1693_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 6, v___x_1707_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 7, v_mulFn_x3f_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 8, v_subFn_x3f_1695_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 9, v_negFn_x3f_1696_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 10, v_powFn_x3f_1697_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 11, v_intCastFn_x3f_1698_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 12, v_natCastFn_x3f_1699_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 13, v_one_x3f_1700_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 14, v_vars_1701_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 15, v_varMap_1702_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 16, v_denote_1703_);
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
    mut v_toPure_1713_: *mut LeanObject,
    mut v_addFn_1714_: *mut LeanObject,
    mut v_____r_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_apply_2(v_toPure_1713_, lean_box(0), v_addFn_1714_);
    return v___x_1716_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2(
    mut v_toPure_1717_: *mut LeanObject,
    mut v_modifyRing_1718_: *mut LeanObject,
    mut v_toBind_1719_: *mut LeanObject,
    mut v_addFn_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_addFn_1720_);
    v___f_1721_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1721_, 0, v_addFn_1720_);
    v___f_1722_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1722_, 0, v_toPure_1717_);
    lean_closure_set(v___f_1722_, 1, v_addFn_1720_);
    v___x_1723_ = lean_apply_1(v_modifyRing_1718_, v___f_1721_);
    v___x_1724_ = lean_apply_4(
        v_toBind_1719_,
        lean_box(0),
        lean_box(0),
        v___x_1723_,
        v___f_1722_,
    );
    return v___x_1724_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(
    mut v_toPure_1741_: *mut LeanObject,
    mut v_inst_1742_: *mut LeanObject,
    mut v_inst_1743_: *mut LeanObject,
    mut v_inst_1744_: *mut LeanObject,
    mut v_inst_1745_: *mut LeanObject,
    mut v_toBind_1746_: *mut LeanObject,
    mut v___f_1747_: *mut LeanObject,
    mut v_ring_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_addFn_x3f_1749_: *mut LeanObject = core::ptr::null_mut();
    v_addFn_x3f_1749_ = lean_ctor_get(v_ring_1748_, 6);
    if lean_obj_tag(v_addFn_x3f_1749_) == 1 {
        let mut v_val_1750_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_addFn_x3f_1749_);
        lean_dec_ref(v_ring_1748_);
        lean_dec(v___f_1747_);
        lean_dec(v_toBind_1746_);
        lean_dec_ref(v_inst_1745_);
        lean_dec_ref(v_inst_1744_);
        lean_dec_ref(v_inst_1743_);
        lean_dec(v_inst_1742_);
        v_val_1750_ = lean_ctor_get(v_addFn_x3f_1749_, 0);
        lean_inc(v_val_1750_);
        lean_dec_ref_known(v_addFn_x3f_1749_, 1);
        v___x_1751_ = lean_apply_2(v_toPure_1741_, lean_box(0), v_val_1750_);
        return v___x_1751_;
    } else {
        let mut v_type_1752_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1741_);
        v_type_1752_ = lean_ctor_get(v_ring_1748_, 1);
        lean_inc_ref_n(v_type_1752_, 3);
        v_u_1753_ = lean_ctor_get(v_ring_1748_, 2);
        lean_inc_n(v_u_1753_, 2);
        v_semiringInst_1754_ = lean_ctor_get(v_ring_1748_, 4);
        lean_inc_ref(v_semiringInst_1754_);
        lean_dec_ref(v_ring_1748_);
        v___x_1755_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1;
        v___x_1756_ = lean_box(0);
        v___x_1757_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1757_, 0, v_u_1753_);
        lean_ctor_set(v___x_1757_, 1, v___x_1756_);
        lean_inc_ref(v___x_1757_);
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
        v___x_1766_ = lean_apply_4(
            v_toBind_1746_,
            lean_box(0),
            lean_box(0),
            v___x_1765_,
            v___f_1747_,
        );
        return v___x_1766_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
    mut v_inst_1767_: *mut LeanObject,
    mut v_inst_1768_: *mut LeanObject,
    mut v_inst_1769_: *mut LeanObject,
    mut v_inst_1770_: *mut LeanObject,
    mut v_inst_1771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1772_ = lean_ctor_get(v_inst_1769_, 0);
    v_toBind_1773_ = lean_ctor_get(v_inst_1769_, 1);
    lean_inc_n(v_toBind_1773_, 3);
    v_getRing_1774_ = lean_ctor_get(v_inst_1771_, 0);
    lean_inc(v_getRing_1774_);
    v_modifyRing_1775_ = lean_ctor_get(v_inst_1771_, 1);
    lean_inc(v_modifyRing_1775_);
    lean_dec_ref(v_inst_1771_);
    v_toPure_1776_ = lean_ctor_get(v_toApplicative_1772_, 1);
    lean_inc_n(v_toPure_1776_, 2);
    v___f_1777_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1777_, 0, v_toPure_1776_);
    lean_closure_set(v___f_1777_, 1, v_modifyRing_1775_);
    lean_closure_set(v___f_1777_, 2, v_toBind_1773_);
    v___f_1778_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1778_, 0, v_toPure_1776_);
    lean_closure_set(v___f_1778_, 1, v_inst_1767_);
    lean_closure_set(v___f_1778_, 2, v_inst_1768_);
    lean_closure_set(v___f_1778_, 3, v_inst_1769_);
    lean_closure_set(v___f_1778_, 4, v_inst_1770_);
    lean_closure_set(v___f_1778_, 5, v_toBind_1773_);
    lean_closure_set(v___f_1778_, 6, v___f_1777_);
    v___x_1779_ = lean_apply_4(
        v_toBind_1773_,
        lean_box(0),
        lean_box(0),
        v_getRing_1774_,
        v___f_1778_,
    );
    return v___x_1779_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn(
    mut v_m_1780_: *mut LeanObject,
    mut v_inst_1781_: *mut LeanObject,
    mut v_inst_1782_: *mut LeanObject,
    mut v_inst_1783_: *mut LeanObject,
    mut v_inst_1784_: *mut LeanObject,
    mut v_inst_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_subFn_1787_: *mut LeanObject,
    mut v_s_1788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1789_ = lean_ctor_get(v_s_1788_, 0);
                v_type_1790_ = lean_ctor_get(v_s_1788_, 1);
                v_u_1791_ = lean_ctor_get(v_s_1788_, 2);
                v_ringInst_1792_ = lean_ctor_get(v_s_1788_, 3);
                v_semiringInst_1793_ = lean_ctor_get(v_s_1788_, 4);
                v_charInst_x3f_1794_ = lean_ctor_get(v_s_1788_, 5);
                v_addFn_x3f_1795_ = lean_ctor_get(v_s_1788_, 6);
                v_mulFn_x3f_1796_ = lean_ctor_get(v_s_1788_, 7);
                v_negFn_x3f_1797_ = lean_ctor_get(v_s_1788_, 9);
                v_powFn_x3f_1798_ = lean_ctor_get(v_s_1788_, 10);
                v_intCastFn_x3f_1799_ = lean_ctor_get(v_s_1788_, 11);
                v_natCastFn_x3f_1800_ = lean_ctor_get(v_s_1788_, 12);
                v_one_x3f_1801_ = lean_ctor_get(v_s_1788_, 13);
                v_vars_1802_ = lean_ctor_get(v_s_1788_, 14);
                v_varMap_1803_ = lean_ctor_get(v_s_1788_, 15);
                v_denote_1804_ = lean_ctor_get(v_s_1788_, 16);
                v_isSharedCheck_1812_ = (!lean_is_exclusive(v_s_1788_)) as u8;
                if v_isSharedCheck_1812_ == 0 {
                    v_unused_1813_ = lean_ctor_get(v_s_1788_, 8);
                    lean_dec(v_unused_1813_);
                    v___x_1806_ = v_s_1788_;
                    v_isShared_1807_ = v_isSharedCheck_1812_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_1804_);
                    lean_inc(v_varMap_1803_);
                    lean_inc(v_vars_1802_);
                    lean_inc(v_one_x3f_1801_);
                    lean_inc(v_natCastFn_x3f_1800_);
                    lean_inc(v_intCastFn_x3f_1799_);
                    lean_inc(v_powFn_x3f_1798_);
                    lean_inc(v_negFn_x3f_1797_);
                    lean_inc(v_mulFn_x3f_1796_);
                    lean_inc(v_addFn_x3f_1795_);
                    lean_inc(v_charInst_x3f_1794_);
                    lean_inc(v_semiringInst_1793_);
                    lean_inc(v_ringInst_1792_);
                    lean_inc(v_u_1791_);
                    lean_inc(v_type_1790_);
                    lean_inc(v_id_1789_);
                    lean_dec(v_s_1788_);
                    v___x_1806_ = lean_box(0);
                    v_isShared_1807_ = v_isSharedCheck_1812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1808_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1808_, 0, v_subFn_1787_);
                if v_isShared_1807_ == 0 {
                    lean_ctor_set(v___x_1806_, 8, v___x_1808_);
                    v___x_1810_ = v___x_1806_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_id_1789_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_type_1790_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_u_1791_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_ringInst_1792_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 4, v_semiringInst_1793_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 5, v_charInst_x3f_1794_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 6, v_addFn_x3f_1795_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 7, v_mulFn_x3f_1796_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 8, v___x_1808_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 9, v_negFn_x3f_1797_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 10, v_powFn_x3f_1798_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 11, v_intCastFn_x3f_1799_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 12, v_natCastFn_x3f_1800_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 13, v_one_x3f_1801_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 14, v_vars_1802_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 15, v_varMap_1803_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 16, v_denote_1804_);
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
    mut v_toPure_1814_: *mut LeanObject,
    mut v_subFn_1815_: *mut LeanObject,
    mut v_____r_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_1817_ = lean_apply_2(v_toPure_1814_, lean_box(0), v_subFn_1815_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2(
    mut v_toPure_1818_: *mut LeanObject,
    mut v_modifyRing_1819_: *mut LeanObject,
    mut v_toBind_1820_: *mut LeanObject,
    mut v_subFn_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_subFn_1821_);
    v___f_1822_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1822_, 0, v_subFn_1821_);
    v___f_1823_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1823_, 0, v_toPure_1818_);
    lean_closure_set(v___f_1823_, 1, v_subFn_1821_);
    v___x_1824_ = lean_apply_1(v_modifyRing_1819_, v___f_1822_);
    v___x_1825_ = lean_apply_4(
        v_toBind_1820_,
        lean_box(0),
        lean_box(0),
        v___x_1824_,
        v___f_1823_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(
    mut v_toPure_1843_: *mut LeanObject,
    mut v_inst_1844_: *mut LeanObject,
    mut v_inst_1845_: *mut LeanObject,
    mut v_inst_1846_: *mut LeanObject,
    mut v_inst_1847_: *mut LeanObject,
    mut v_toBind_1848_: *mut LeanObject,
    mut v___f_1849_: *mut LeanObject,
    mut v_ring_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subFn_x3f_1851_: *mut LeanObject = core::ptr::null_mut();
    v_subFn_x3f_1851_ = lean_ctor_get(v_ring_1850_, 8);
    if lean_obj_tag(v_subFn_x3f_1851_) == 1 {
        let mut v_val_1852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_subFn_x3f_1851_);
        lean_dec_ref(v_ring_1850_);
        lean_dec(v___f_1849_);
        lean_dec(v_toBind_1848_);
        lean_dec_ref(v_inst_1847_);
        lean_dec_ref(v_inst_1846_);
        lean_dec_ref(v_inst_1845_);
        lean_dec(v_inst_1844_);
        v_val_1852_ = lean_ctor_get(v_subFn_x3f_1851_, 0);
        lean_inc(v_val_1852_);
        lean_dec_ref_known(v_subFn_x3f_1851_, 1);
        v___x_1853_ = lean_apply_2(v_toPure_1843_, lean_box(0), v_val_1852_);
        return v___x_1853_;
    } else {
        let mut v_type_1854_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_1855_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ringInst_1856_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1864_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1843_);
        v_type_1854_ = lean_ctor_get(v_ring_1850_, 1);
        lean_inc_ref_n(v_type_1854_, 3);
        v_u_1855_ = lean_ctor_get(v_ring_1850_, 2);
        lean_inc_n(v_u_1855_, 2);
        v_ringInst_1856_ = lean_ctor_get(v_ring_1850_, 3);
        lean_inc_ref(v_ringInst_1856_);
        lean_dec_ref(v_ring_1850_);
        v___x_1857_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1;
        v___x_1858_ = lean_box(0);
        v___x_1859_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1859_, 0, v_u_1855_);
        lean_ctor_set(v___x_1859_, 1, v___x_1858_);
        lean_inc_ref(v___x_1859_);
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
        v___x_1868_ = lean_apply_4(
            v_toBind_1848_,
            lean_box(0),
            lean_box(0),
            v___x_1867_,
            v___f_1849_,
        );
        return v___x_1868_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(
    mut v_inst_1869_: *mut LeanObject,
    mut v_inst_1870_: *mut LeanObject,
    mut v_inst_1871_: *mut LeanObject,
    mut v_inst_1872_: *mut LeanObject,
    mut v_inst_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1874_ = lean_ctor_get(v_inst_1871_, 0);
    v_toBind_1875_ = lean_ctor_get(v_inst_1871_, 1);
    lean_inc_n(v_toBind_1875_, 3);
    v_getRing_1876_ = lean_ctor_get(v_inst_1873_, 0);
    lean_inc(v_getRing_1876_);
    v_modifyRing_1877_ = lean_ctor_get(v_inst_1873_, 1);
    lean_inc(v_modifyRing_1877_);
    lean_dec_ref(v_inst_1873_);
    v_toPure_1878_ = lean_ctor_get(v_toApplicative_1874_, 1);
    lean_inc_n(v_toPure_1878_, 2);
    v___f_1879_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1879_, 0, v_toPure_1878_);
    lean_closure_set(v___f_1879_, 1, v_modifyRing_1877_);
    lean_closure_set(v___f_1879_, 2, v_toBind_1875_);
    v___f_1880_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1880_, 0, v_toPure_1878_);
    lean_closure_set(v___f_1880_, 1, v_inst_1869_);
    lean_closure_set(v___f_1880_, 2, v_inst_1870_);
    lean_closure_set(v___f_1880_, 3, v_inst_1871_);
    lean_closure_set(v___f_1880_, 4, v_inst_1872_);
    lean_closure_set(v___f_1880_, 5, v_toBind_1875_);
    lean_closure_set(v___f_1880_, 6, v___f_1879_);
    v___x_1881_ = lean_apply_4(
        v_toBind_1875_,
        lean_box(0),
        lean_box(0),
        v_getRing_1876_,
        v___f_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn(
    mut v_m_1882_: *mut LeanObject,
    mut v_inst_1883_: *mut LeanObject,
    mut v_inst_1884_: *mut LeanObject,
    mut v_inst_1885_: *mut LeanObject,
    mut v_inst_1886_: *mut LeanObject,
    mut v_inst_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_mulFn_1889_: *mut LeanObject,
    mut v_s_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1914_: u8 = 0;
    let mut v_unused_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1891_ = lean_ctor_get(v_s_1890_, 0);
                v_type_1892_ = lean_ctor_get(v_s_1890_, 1);
                v_u_1893_ = lean_ctor_get(v_s_1890_, 2);
                v_ringInst_1894_ = lean_ctor_get(v_s_1890_, 3);
                v_semiringInst_1895_ = lean_ctor_get(v_s_1890_, 4);
                v_charInst_x3f_1896_ = lean_ctor_get(v_s_1890_, 5);
                v_addFn_x3f_1897_ = lean_ctor_get(v_s_1890_, 6);
                v_subFn_x3f_1898_ = lean_ctor_get(v_s_1890_, 8);
                v_negFn_x3f_1899_ = lean_ctor_get(v_s_1890_, 9);
                v_powFn_x3f_1900_ = lean_ctor_get(v_s_1890_, 10);
                v_intCastFn_x3f_1901_ = lean_ctor_get(v_s_1890_, 11);
                v_natCastFn_x3f_1902_ = lean_ctor_get(v_s_1890_, 12);
                v_one_x3f_1903_ = lean_ctor_get(v_s_1890_, 13);
                v_vars_1904_ = lean_ctor_get(v_s_1890_, 14);
                v_varMap_1905_ = lean_ctor_get(v_s_1890_, 15);
                v_denote_1906_ = lean_ctor_get(v_s_1890_, 16);
                v_isSharedCheck_1914_ = (!lean_is_exclusive(v_s_1890_)) as u8;
                if v_isSharedCheck_1914_ == 0 {
                    v_unused_1915_ = lean_ctor_get(v_s_1890_, 7);
                    lean_dec(v_unused_1915_);
                    v___x_1908_ = v_s_1890_;
                    v_isShared_1909_ = v_isSharedCheck_1914_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_1906_);
                    lean_inc(v_varMap_1905_);
                    lean_inc(v_vars_1904_);
                    lean_inc(v_one_x3f_1903_);
                    lean_inc(v_natCastFn_x3f_1902_);
                    lean_inc(v_intCastFn_x3f_1901_);
                    lean_inc(v_powFn_x3f_1900_);
                    lean_inc(v_negFn_x3f_1899_);
                    lean_inc(v_subFn_x3f_1898_);
                    lean_inc(v_addFn_x3f_1897_);
                    lean_inc(v_charInst_x3f_1896_);
                    lean_inc(v_semiringInst_1895_);
                    lean_inc(v_ringInst_1894_);
                    lean_inc(v_u_1893_);
                    lean_inc(v_type_1892_);
                    lean_inc(v_id_1891_);
                    lean_dec(v_s_1890_);
                    v___x_1908_ = lean_box(0);
                    v_isShared_1909_ = v_isSharedCheck_1914_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1910_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1910_, 0, v_mulFn_1889_);
                if v_isShared_1909_ == 0 {
                    lean_ctor_set(v___x_1908_, 7, v___x_1910_);
                    v___x_1912_ = v___x_1908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_id_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_type_1892_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_u_1893_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_ringInst_1894_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_semiringInst_1895_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_charInst_x3f_1896_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 6, v_addFn_x3f_1897_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 7, v___x_1910_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 8, v_subFn_x3f_1898_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 9, v_negFn_x3f_1899_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 10, v_powFn_x3f_1900_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 11, v_intCastFn_x3f_1901_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 12, v_natCastFn_x3f_1902_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 13, v_one_x3f_1903_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 14, v_vars_1904_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 15, v_varMap_1905_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 16, v_denote_1906_);
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
    mut v_toPure_1916_: *mut LeanObject,
    mut v_mulFn_1917_: *mut LeanObject,
    mut v_____r_1918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    v___x_1919_ = lean_apply_2(v_toPure_1916_, lean_box(0), v_mulFn_1917_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2(
    mut v_toPure_1920_: *mut LeanObject,
    mut v_modifyRing_1921_: *mut LeanObject,
    mut v_toBind_1922_: *mut LeanObject,
    mut v_mulFn_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_mulFn_1923_);
    v___f_1924_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1924_, 0, v_mulFn_1923_);
    v___f_1925_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1925_, 0, v_toPure_1920_);
    lean_closure_set(v___f_1925_, 1, v_mulFn_1923_);
    v___x_1926_ = lean_apply_1(v_modifyRing_1921_, v___f_1924_);
    v___x_1927_ = lean_apply_4(
        v_toBind_1922_,
        lean_box(0),
        lean_box(0),
        v___x_1926_,
        v___f_1925_,
    );
    return v___x_1927_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(
    mut v_toPure_1944_: *mut LeanObject,
    mut v_inst_1945_: *mut LeanObject,
    mut v_inst_1946_: *mut LeanObject,
    mut v_inst_1947_: *mut LeanObject,
    mut v_inst_1948_: *mut LeanObject,
    mut v_toBind_1949_: *mut LeanObject,
    mut v___f_1950_: *mut LeanObject,
    mut v_ring_1951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mulFn_x3f_1952_: *mut LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_1952_ = lean_ctor_get(v_ring_1951_, 7);
    if lean_obj_tag(v_mulFn_x3f_1952_) == 1 {
        let mut v_val_1953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_mulFn_x3f_1952_);
        lean_dec_ref(v_ring_1951_);
        lean_dec(v___f_1950_);
        lean_dec(v_toBind_1949_);
        lean_dec_ref(v_inst_1948_);
        lean_dec_ref(v_inst_1947_);
        lean_dec_ref(v_inst_1946_);
        lean_dec(v_inst_1945_);
        v_val_1953_ = lean_ctor_get(v_mulFn_x3f_1952_, 0);
        lean_inc(v_val_1953_);
        lean_dec_ref_known(v_mulFn_x3f_1952_, 1);
        v___x_1954_ = lean_apply_2(v_toPure_1944_, lean_box(0), v_val_1953_);
        return v___x_1954_;
    } else {
        let mut v_type_1955_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_1956_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1957_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1965_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1944_);
        v_type_1955_ = lean_ctor_get(v_ring_1951_, 1);
        lean_inc_ref_n(v_type_1955_, 3);
        v_u_1956_ = lean_ctor_get(v_ring_1951_, 2);
        lean_inc_n(v_u_1956_, 2);
        v_semiringInst_1957_ = lean_ctor_get(v_ring_1951_, 4);
        lean_inc_ref(v_semiringInst_1957_);
        lean_dec_ref(v_ring_1951_);
        v___x_1958_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1;
        v___x_1959_ = lean_box(0);
        v___x_1960_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1960_, 0, v_u_1956_);
        lean_ctor_set(v___x_1960_, 1, v___x_1959_);
        lean_inc_ref(v___x_1960_);
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
        v___x_1969_ = lean_apply_4(
            v_toBind_1949_,
            lean_box(0),
            lean_box(0),
            v___x_1968_,
            v___f_1950_,
        );
        return v___x_1969_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
    mut v_inst_1970_: *mut LeanObject,
    mut v_inst_1971_: *mut LeanObject,
    mut v_inst_1972_: *mut LeanObject,
    mut v_inst_1973_: *mut LeanObject,
    mut v_inst_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1975_ = lean_ctor_get(v_inst_1972_, 0);
    v_toBind_1976_ = lean_ctor_get(v_inst_1972_, 1);
    lean_inc_n(v_toBind_1976_, 3);
    v_getRing_1977_ = lean_ctor_get(v_inst_1974_, 0);
    lean_inc(v_getRing_1977_);
    v_modifyRing_1978_ = lean_ctor_get(v_inst_1974_, 1);
    lean_inc(v_modifyRing_1978_);
    lean_dec_ref(v_inst_1974_);
    v_toPure_1979_ = lean_ctor_get(v_toApplicative_1975_, 1);
    lean_inc_n(v_toPure_1979_, 2);
    v___f_1980_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1980_, 0, v_toPure_1979_);
    lean_closure_set(v___f_1980_, 1, v_modifyRing_1978_);
    lean_closure_set(v___f_1980_, 2, v_toBind_1976_);
    v___f_1981_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1981_, 0, v_toPure_1979_);
    lean_closure_set(v___f_1981_, 1, v_inst_1970_);
    lean_closure_set(v___f_1981_, 2, v_inst_1971_);
    lean_closure_set(v___f_1981_, 3, v_inst_1972_);
    lean_closure_set(v___f_1981_, 4, v_inst_1973_);
    lean_closure_set(v___f_1981_, 5, v_toBind_1976_);
    lean_closure_set(v___f_1981_, 6, v___f_1980_);
    v___x_1982_ = lean_apply_4(
        v_toBind_1976_,
        lean_box(0),
        lean_box(0),
        v_getRing_1977_,
        v___f_1981_,
    );
    return v___x_1982_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn(
    mut v_m_1983_: *mut LeanObject,
    mut v_inst_1984_: *mut LeanObject,
    mut v_inst_1985_: *mut LeanObject,
    mut v_inst_1986_: *mut LeanObject,
    mut v_inst_1987_: *mut LeanObject,
    mut v_inst_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_negFn_1990_: *mut LeanObject,
    mut v_s_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_unused_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1992_ = lean_ctor_get(v_s_1991_, 0);
                v_type_1993_ = lean_ctor_get(v_s_1991_, 1);
                v_u_1994_ = lean_ctor_get(v_s_1991_, 2);
                v_ringInst_1995_ = lean_ctor_get(v_s_1991_, 3);
                v_semiringInst_1996_ = lean_ctor_get(v_s_1991_, 4);
                v_charInst_x3f_1997_ = lean_ctor_get(v_s_1991_, 5);
                v_addFn_x3f_1998_ = lean_ctor_get(v_s_1991_, 6);
                v_mulFn_x3f_1999_ = lean_ctor_get(v_s_1991_, 7);
                v_subFn_x3f_2000_ = lean_ctor_get(v_s_1991_, 8);
                v_powFn_x3f_2001_ = lean_ctor_get(v_s_1991_, 10);
                v_intCastFn_x3f_2002_ = lean_ctor_get(v_s_1991_, 11);
                v_natCastFn_x3f_2003_ = lean_ctor_get(v_s_1991_, 12);
                v_one_x3f_2004_ = lean_ctor_get(v_s_1991_, 13);
                v_vars_2005_ = lean_ctor_get(v_s_1991_, 14);
                v_varMap_2006_ = lean_ctor_get(v_s_1991_, 15);
                v_denote_2007_ = lean_ctor_get(v_s_1991_, 16);
                v_isSharedCheck_2015_ = (!lean_is_exclusive(v_s_1991_)) as u8;
                if v_isSharedCheck_2015_ == 0 {
                    v_unused_2016_ = lean_ctor_get(v_s_1991_, 9);
                    lean_dec(v_unused_2016_);
                    v___x_2009_ = v_s_1991_;
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_2007_);
                    lean_inc(v_varMap_2006_);
                    lean_inc(v_vars_2005_);
                    lean_inc(v_one_x3f_2004_);
                    lean_inc(v_natCastFn_x3f_2003_);
                    lean_inc(v_intCastFn_x3f_2002_);
                    lean_inc(v_powFn_x3f_2001_);
                    lean_inc(v_subFn_x3f_2000_);
                    lean_inc(v_mulFn_x3f_1999_);
                    lean_inc(v_addFn_x3f_1998_);
                    lean_inc(v_charInst_x3f_1997_);
                    lean_inc(v_semiringInst_1996_);
                    lean_inc(v_ringInst_1995_);
                    lean_inc(v_u_1994_);
                    lean_inc(v_type_1993_);
                    lean_inc(v_id_1992_);
                    lean_dec(v_s_1991_);
                    v___x_2009_ = lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2011_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2011_, 0, v_negFn_1990_);
                if v_isShared_2010_ == 0 {
                    lean_ctor_set(v___x_2009_, 9, v___x_2011_);
                    v___x_2013_ = v___x_2009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_id_1992_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_type_1993_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_u_1994_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_ringInst_1995_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_semiringInst_1996_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_charInst_x3f_1997_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_addFn_x3f_1998_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_mulFn_x3f_1999_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_subFn_x3f_2000_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 9, v___x_2011_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 10, v_powFn_x3f_2001_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 11, v_intCastFn_x3f_2002_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 12, v_natCastFn_x3f_2003_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 13, v_one_x3f_2004_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 14, v_vars_2005_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 15, v_varMap_2006_);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 16, v_denote_2007_);
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
    mut v_toPure_2017_: *mut LeanObject,
    mut v_negFn_2018_: *mut LeanObject,
    mut v_____r_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    v___x_2020_ = lean_apply_2(v_toPure_2017_, lean_box(0), v_negFn_2018_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2(
    mut v_toPure_2021_: *mut LeanObject,
    mut v_modifyRing_2022_: *mut LeanObject,
    mut v_toBind_2023_: *mut LeanObject,
    mut v_negFn_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_negFn_2024_);
    v___f_2025_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2025_, 0, v_negFn_2024_);
    v___f_2026_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2026_, 0, v_toPure_2021_);
    lean_closure_set(v___f_2026_, 1, v_negFn_2024_);
    v___x_2027_ = lean_apply_1(v_modifyRing_2022_, v___f_2025_);
    v___x_2028_ = lean_apply_4(
        v_toBind_2023_,
        lean_box(0),
        lean_box(0),
        v___x_2027_,
        v___f_2026_,
    );
    return v___x_2028_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(
    mut v_toPure_2042_: *mut LeanObject,
    mut v_inst_2043_: *mut LeanObject,
    mut v_inst_2044_: *mut LeanObject,
    mut v_inst_2045_: *mut LeanObject,
    mut v_inst_2046_: *mut LeanObject,
    mut v_toBind_2047_: *mut LeanObject,
    mut v___f_2048_: *mut LeanObject,
    mut v_ring_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_negFn_x3f_2050_: *mut LeanObject = core::ptr::null_mut();
    v_negFn_x3f_2050_ = lean_ctor_get(v_ring_2049_, 9);
    if lean_obj_tag(v_negFn_x3f_2050_) == 1 {
        let mut v_val_2051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_negFn_x3f_2050_);
        lean_dec_ref(v_ring_2049_);
        lean_dec(v___f_2048_);
        lean_dec(v_toBind_2047_);
        lean_dec_ref(v_inst_2046_);
        lean_dec_ref(v_inst_2045_);
        lean_dec_ref(v_inst_2044_);
        lean_dec(v_inst_2043_);
        v_val_2051_ = lean_ctor_get(v_negFn_x3f_2050_, 0);
        lean_inc(v_val_2051_);
        lean_dec_ref_known(v_negFn_x3f_2050_, 1);
        v___x_2052_ = lean_apply_2(v_toPure_2042_, lean_box(0), v_val_2051_);
        return v___x_2052_;
    } else {
        let mut v_type_2053_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2054_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ringInst_2055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2060_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2042_);
        v_type_2053_ = lean_ctor_get(v_ring_2049_, 1);
        lean_inc_ref_n(v_type_2053_, 2);
        v_u_2054_ = lean_ctor_get(v_ring_2049_, 2);
        lean_inc_n(v_u_2054_, 2);
        v_ringInst_2055_ = lean_ctor_get(v_ring_2049_, 3);
        lean_inc_ref(v_ringInst_2055_);
        lean_dec_ref(v_ring_2049_);
        v___x_2056_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1;
        v___x_2057_ = lean_box(0);
        v___x_2058_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2058_, 0, v_u_2054_);
        lean_ctor_set(v___x_2058_, 1, v___x_2057_);
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
        v___x_2064_ = lean_apply_4(
            v_toBind_2047_,
            lean_box(0),
            lean_box(0),
            v___x_2063_,
            v___f_2048_,
        );
        return v___x_2064_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
    mut v_inst_2065_: *mut LeanObject,
    mut v_inst_2066_: *mut LeanObject,
    mut v_inst_2067_: *mut LeanObject,
    mut v_inst_2068_: *mut LeanObject,
    mut v_inst_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2070_ = lean_ctor_get(v_inst_2067_, 0);
    v_toBind_2071_ = lean_ctor_get(v_inst_2067_, 1);
    lean_inc_n(v_toBind_2071_, 3);
    v_getRing_2072_ = lean_ctor_get(v_inst_2069_, 0);
    lean_inc(v_getRing_2072_);
    v_modifyRing_2073_ = lean_ctor_get(v_inst_2069_, 1);
    lean_inc(v_modifyRing_2073_);
    lean_dec_ref(v_inst_2069_);
    v_toPure_2074_ = lean_ctor_get(v_toApplicative_2070_, 1);
    lean_inc_n(v_toPure_2074_, 2);
    v___f_2075_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2075_, 0, v_toPure_2074_);
    lean_closure_set(v___f_2075_, 1, v_modifyRing_2073_);
    lean_closure_set(v___f_2075_, 2, v_toBind_2071_);
    v___f_2076_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2076_, 0, v_toPure_2074_);
    lean_closure_set(v___f_2076_, 1, v_inst_2065_);
    lean_closure_set(v___f_2076_, 2, v_inst_2066_);
    lean_closure_set(v___f_2076_, 3, v_inst_2067_);
    lean_closure_set(v___f_2076_, 4, v_inst_2068_);
    lean_closure_set(v___f_2076_, 5, v_toBind_2071_);
    lean_closure_set(v___f_2076_, 6, v___f_2075_);
    v___x_2077_ = lean_apply_4(
        v_toBind_2071_,
        lean_box(0),
        lean_box(0),
        v_getRing_2072_,
        v___f_2076_,
    );
    return v___x_2077_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn(
    mut v_m_2078_: *mut LeanObject,
    mut v_inst_2079_: *mut LeanObject,
    mut v_inst_2080_: *mut LeanObject,
    mut v_inst_2081_: *mut LeanObject,
    mut v_inst_2082_: *mut LeanObject,
    mut v_inst_2083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_powFn_2085_: *mut LeanObject,
    mut v_s_2086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2105_: u8 = 0;
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_unused_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2087_ = lean_ctor_get(v_s_2086_, 0);
                v_type_2088_ = lean_ctor_get(v_s_2086_, 1);
                v_u_2089_ = lean_ctor_get(v_s_2086_, 2);
                v_ringInst_2090_ = lean_ctor_get(v_s_2086_, 3);
                v_semiringInst_2091_ = lean_ctor_get(v_s_2086_, 4);
                v_charInst_x3f_2092_ = lean_ctor_get(v_s_2086_, 5);
                v_addFn_x3f_2093_ = lean_ctor_get(v_s_2086_, 6);
                v_mulFn_x3f_2094_ = lean_ctor_get(v_s_2086_, 7);
                v_subFn_x3f_2095_ = lean_ctor_get(v_s_2086_, 8);
                v_negFn_x3f_2096_ = lean_ctor_get(v_s_2086_, 9);
                v_intCastFn_x3f_2097_ = lean_ctor_get(v_s_2086_, 11);
                v_natCastFn_x3f_2098_ = lean_ctor_get(v_s_2086_, 12);
                v_one_x3f_2099_ = lean_ctor_get(v_s_2086_, 13);
                v_vars_2100_ = lean_ctor_get(v_s_2086_, 14);
                v_varMap_2101_ = lean_ctor_get(v_s_2086_, 15);
                v_denote_2102_ = lean_ctor_get(v_s_2086_, 16);
                v_isSharedCheck_2110_ = (!lean_is_exclusive(v_s_2086_)) as u8;
                if v_isSharedCheck_2110_ == 0 {
                    v_unused_2111_ = lean_ctor_get(v_s_2086_, 10);
                    lean_dec(v_unused_2111_);
                    v___x_2104_ = v_s_2086_;
                    v_isShared_2105_ = v_isSharedCheck_2110_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_2102_);
                    lean_inc(v_varMap_2101_);
                    lean_inc(v_vars_2100_);
                    lean_inc(v_one_x3f_2099_);
                    lean_inc(v_natCastFn_x3f_2098_);
                    lean_inc(v_intCastFn_x3f_2097_);
                    lean_inc(v_negFn_x3f_2096_);
                    lean_inc(v_subFn_x3f_2095_);
                    lean_inc(v_mulFn_x3f_2094_);
                    lean_inc(v_addFn_x3f_2093_);
                    lean_inc(v_charInst_x3f_2092_);
                    lean_inc(v_semiringInst_2091_);
                    lean_inc(v_ringInst_2090_);
                    lean_inc(v_u_2089_);
                    lean_inc(v_type_2088_);
                    lean_inc(v_id_2087_);
                    lean_dec(v_s_2086_);
                    v___x_2104_ = lean_box(0);
                    v_isShared_2105_ = v_isSharedCheck_2110_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2106_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2106_, 0, v_powFn_2085_);
                if v_isShared_2105_ == 0 {
                    lean_ctor_set(v___x_2104_, 10, v___x_2106_);
                    v___x_2108_ = v___x_2104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_id_2087_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_type_2088_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_u_2089_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_ringInst_2090_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_semiringInst_2091_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 5, v_charInst_x3f_2092_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 6, v_addFn_x3f_2093_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 7, v_mulFn_x3f_2094_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 8, v_subFn_x3f_2095_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 9, v_negFn_x3f_2096_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 10, v___x_2106_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 11, v_intCastFn_x3f_2097_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 12, v_natCastFn_x3f_2098_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 13, v_one_x3f_2099_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 14, v_vars_2100_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 15, v_varMap_2101_);
                    lean_ctor_set(v_reuseFailAlloc_2109_, 16, v_denote_2102_);
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
    mut v_toPure_2112_: *mut LeanObject,
    mut v_powFn_2113_: *mut LeanObject,
    mut v_____r_2114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    v___x_2115_ = lean_apply_2(v_toPure_2112_, lean_box(0), v_powFn_2113_);
    return v___x_2115_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(
    mut v_toPure_2116_: *mut LeanObject,
    mut v_modifyRing_2117_: *mut LeanObject,
    mut v_toBind_2118_: *mut LeanObject,
    mut v_powFn_2119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_powFn_2119_);
    v___f_2120_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2120_, 0, v_powFn_2119_);
    v___f_2121_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2121_, 0, v_toPure_2116_);
    lean_closure_set(v___f_2121_, 1, v_powFn_2119_);
    v___x_2122_ = lean_apply_1(v_modifyRing_2117_, v___f_2120_);
    v___x_2123_ = lean_apply_4(
        v_toBind_2118_,
        lean_box(0),
        lean_box(0),
        v___x_2122_,
        v___f_2121_,
    );
    return v___x_2123_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(
    mut v_toPure_2124_: *mut LeanObject,
    mut v_inst_2125_: *mut LeanObject,
    mut v_inst_2126_: *mut LeanObject,
    mut v_inst_2127_: *mut LeanObject,
    mut v_inst_2128_: *mut LeanObject,
    mut v_toBind_2129_: *mut LeanObject,
    mut v___f_2130_: *mut LeanObject,
    mut v_ring_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_powFn_x3f_2132_: *mut LeanObject = core::ptr::null_mut();
    v_powFn_x3f_2132_ = lean_ctor_get(v_ring_2131_, 10);
    if lean_obj_tag(v_powFn_x3f_2132_) == 1 {
        let mut v_val_2133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_powFn_x3f_2132_);
        lean_dec_ref(v_ring_2131_);
        lean_dec(v___f_2130_);
        lean_dec(v_toBind_2129_);
        lean_dec_ref(v_inst_2128_);
        lean_dec_ref(v_inst_2127_);
        lean_dec_ref(v_inst_2126_);
        lean_dec(v_inst_2125_);
        v_val_2133_ = lean_ctor_get(v_powFn_x3f_2132_, 0);
        lean_inc(v_val_2133_);
        lean_dec_ref_known(v_powFn_x3f_2132_, 1);
        v___x_2134_ = lean_apply_2(v_toPure_2124_, lean_box(0), v_val_2133_);
        return v___x_2134_;
    } else {
        let mut v_type_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2136_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2124_);
        v_type_2135_ = lean_ctor_get(v_ring_2131_, 1);
        lean_inc_ref(v_type_2135_);
        v_u_2136_ = lean_ctor_get(v_ring_2131_, 2);
        lean_inc(v_u_2136_);
        v_semiringInst_2137_ = lean_ctor_get(v_ring_2131_, 4);
        lean_inc_ref(v_semiringInst_2137_);
        lean_dec_ref(v_ring_2131_);
        v___x_2138_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
            v_inst_2125_,
            v_inst_2126_,
            v_inst_2127_,
            v_inst_2128_,
            v_u_2136_,
            v_type_2135_,
            v_semiringInst_2137_,
        );
        v___x_2139_ = lean_apply_4(
            v_toBind_2129_,
            lean_box(0),
            lean_box(0),
            v___x_2138_,
            v___f_2130_,
        );
        return v___x_2139_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
    mut v_inst_2140_: *mut LeanObject,
    mut v_inst_2141_: *mut LeanObject,
    mut v_inst_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_inst_2144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2145_ = lean_ctor_get(v_inst_2142_, 0);
    v_toBind_2146_ = lean_ctor_get(v_inst_2142_, 1);
    lean_inc_n(v_toBind_2146_, 3);
    v_getRing_2147_ = lean_ctor_get(v_inst_2144_, 0);
    lean_inc(v_getRing_2147_);
    v_modifyRing_2148_ = lean_ctor_get(v_inst_2144_, 1);
    lean_inc(v_modifyRing_2148_);
    lean_dec_ref(v_inst_2144_);
    v_toPure_2149_ = lean_ctor_get(v_toApplicative_2145_, 1);
    lean_inc_n(v_toPure_2149_, 2);
    v___f_2150_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2150_, 0, v_toPure_2149_);
    lean_closure_set(v___f_2150_, 1, v_modifyRing_2148_);
    lean_closure_set(v___f_2150_, 2, v_toBind_2146_);
    v___f_2151_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2151_, 0, v_toPure_2149_);
    lean_closure_set(v___f_2151_, 1, v_inst_2140_);
    lean_closure_set(v___f_2151_, 2, v_inst_2141_);
    lean_closure_set(v___f_2151_, 3, v_inst_2142_);
    lean_closure_set(v___f_2151_, 4, v_inst_2143_);
    lean_closure_set(v___f_2151_, 5, v_toBind_2146_);
    lean_closure_set(v___f_2151_, 6, v___f_2150_);
    v___x_2152_ = lean_apply_4(
        v_toBind_2146_,
        lean_box(0),
        lean_box(0),
        v_getRing_2147_,
        v___f_2151_,
    );
    return v___x_2152_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn(
    mut v_m_2153_: *mut LeanObject,
    mut v_inst_2154_: *mut LeanObject,
    mut v_inst_2155_: *mut LeanObject,
    mut v_inst_2156_: *mut LeanObject,
    mut v_inst_2157_: *mut LeanObject,
    mut v_inst_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_intCastFn_2160_: *mut LeanObject,
    mut v_s_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_unused_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2162_ = lean_ctor_get(v_s_2161_, 0);
                v_type_2163_ = lean_ctor_get(v_s_2161_, 1);
                v_u_2164_ = lean_ctor_get(v_s_2161_, 2);
                v_ringInst_2165_ = lean_ctor_get(v_s_2161_, 3);
                v_semiringInst_2166_ = lean_ctor_get(v_s_2161_, 4);
                v_charInst_x3f_2167_ = lean_ctor_get(v_s_2161_, 5);
                v_addFn_x3f_2168_ = lean_ctor_get(v_s_2161_, 6);
                v_mulFn_x3f_2169_ = lean_ctor_get(v_s_2161_, 7);
                v_subFn_x3f_2170_ = lean_ctor_get(v_s_2161_, 8);
                v_negFn_x3f_2171_ = lean_ctor_get(v_s_2161_, 9);
                v_powFn_x3f_2172_ = lean_ctor_get(v_s_2161_, 10);
                v_natCastFn_x3f_2173_ = lean_ctor_get(v_s_2161_, 12);
                v_one_x3f_2174_ = lean_ctor_get(v_s_2161_, 13);
                v_vars_2175_ = lean_ctor_get(v_s_2161_, 14);
                v_varMap_2176_ = lean_ctor_get(v_s_2161_, 15);
                v_denote_2177_ = lean_ctor_get(v_s_2161_, 16);
                v_isSharedCheck_2185_ = (!lean_is_exclusive(v_s_2161_)) as u8;
                if v_isSharedCheck_2185_ == 0 {
                    v_unused_2186_ = lean_ctor_get(v_s_2161_, 11);
                    lean_dec(v_unused_2186_);
                    v___x_2179_ = v_s_2161_;
                    v_isShared_2180_ = v_isSharedCheck_2185_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_2177_);
                    lean_inc(v_varMap_2176_);
                    lean_inc(v_vars_2175_);
                    lean_inc(v_one_x3f_2174_);
                    lean_inc(v_natCastFn_x3f_2173_);
                    lean_inc(v_powFn_x3f_2172_);
                    lean_inc(v_negFn_x3f_2171_);
                    lean_inc(v_subFn_x3f_2170_);
                    lean_inc(v_mulFn_x3f_2169_);
                    lean_inc(v_addFn_x3f_2168_);
                    lean_inc(v_charInst_x3f_2167_);
                    lean_inc(v_semiringInst_2166_);
                    lean_inc(v_ringInst_2165_);
                    lean_inc(v_u_2164_);
                    lean_inc(v_type_2163_);
                    lean_inc(v_id_2162_);
                    lean_dec(v_s_2161_);
                    v___x_2179_ = lean_box(0);
                    v_isShared_2180_ = v_isSharedCheck_2185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2181_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2181_, 0, v_intCastFn_2160_);
                if v_isShared_2180_ == 0 {
                    lean_ctor_set(v___x_2179_, 11, v___x_2181_);
                    v___x_2183_ = v___x_2179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_id_2162_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_type_2163_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_u_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 3, v_ringInst_2165_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_semiringInst_2166_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 5, v_charInst_x3f_2167_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 6, v_addFn_x3f_2168_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 7, v_mulFn_x3f_2169_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 8, v_subFn_x3f_2170_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 9, v_negFn_x3f_2171_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 10, v_powFn_x3f_2172_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 11, v___x_2181_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 12, v_natCastFn_x3f_2173_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 13, v_one_x3f_2174_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 14, v_vars_2175_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 15, v_varMap_2176_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 16, v_denote_2177_);
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
    mut v_toPure_2187_: *mut LeanObject,
    mut v_intCastFn_2188_: *mut LeanObject,
    mut v_____r_2189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    v___x_2190_ = lean_apply_2(v_toPure_2187_, lean_box(0), v_intCastFn_2188_);
    return v___x_2190_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2(
    mut v_toPure_2191_: *mut LeanObject,
    mut v_modifyRing_2192_: *mut LeanObject,
    mut v_toBind_2193_: *mut LeanObject,
    mut v_intCastFn_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_intCastFn_2194_);
    v___f_2195_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2195_, 0, v_intCastFn_2194_);
    v___f_2196_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2196_, 0, v_toPure_2191_);
    lean_closure_set(v___f_2196_, 1, v_intCastFn_2194_);
    v___x_2197_ = lean_apply_1(v_modifyRing_2192_, v___f_2195_);
    v___x_2198_ = lean_apply_4(
        v_toBind_2193_,
        lean_box(0),
        lean_box(0),
        v___x_2197_,
        v___f_2196_,
    );
    return v___x_2198_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3(
    mut v___x_2199_: *mut LeanObject,
    mut v___x_2200_: *mut LeanObject,
    mut v___x_2201_: *mut LeanObject,
    mut v_type_2202_: *mut LeanObject,
    mut v_canonExpr_2203_: *mut LeanObject,
    mut v_toBind_2204_: *mut LeanObject,
    mut v___f_2205_: *mut LeanObject,
    mut v_inst_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    v___x_2207_ = l_Lean_Name_mkStr2(v___x_2199_, v___x_2200_);
    v___x_2208_ = l_Lean_mkConst(v___x_2207_, v___x_2201_);
    v___x_2209_ = l_Lean_mkAppB(v___x_2208_, v_type_2202_, v_inst_2206_);
    v___x_2210_ = lean_apply_1(v_canonExpr_2203_, v___x_2209_);
    v___x_2211_ = lean_apply_4(
        v_toBind_2204_,
        lean_box(0),
        lean_box(0),
        v___x_2210_,
        v___f_2205_,
    );
    return v___x_2211_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7(
    mut v_toPure_2217_: *mut LeanObject,
    mut v_inst_x27_2218_: *mut LeanObject,
    mut v_toBind_2219_: *mut LeanObject,
    mut v___f_2220_: *mut LeanObject,
    mut v___f_2221_: *mut LeanObject,
    mut v_inst_2222_: *mut LeanObject,
    mut v_____do__lift_2223_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2223_) == 0 {
        let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_2222_);
        lean_dec(v___f_2221_);
        v___x_2224_ = lean_apply_2(v_toPure_2217_, lean_box(0), v_inst_x27_2218_);
        v___x_2225_ = lean_apply_4(
            v_toBind_2219_,
            lean_box(0),
            lean_box(0),
            v___x_2224_,
            v___f_2220_,
        );
        return v___x_2225_;
    } else {
        let mut v_val_2226_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2220_);
        v_val_2226_ = lean_ctor_get(v_____do__lift_2223_, 0);
        lean_inc_n(v_val_2226_, 2);
        lean_dec_ref_known(v_____do__lift_2223_, 1);
        lean_inc(v_toBind_2219_);
        v___f_2227_ = lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_2227_, 0, v_toPure_2217_);
        lean_closure_set(v___f_2227_, 1, v_val_2226_);
        lean_closure_set(v___f_2227_, 2, v_toBind_2219_);
        lean_closure_set(v___f_2227_, 3, v___f_2221_);
        v___x_2228_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2;
        v___x_2229_ = lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        lean_closure_set(v___x_2229_, 0, v___x_2228_);
        lean_closure_set(v___x_2229_, 1, v_val_2226_);
        lean_closure_set(v___x_2229_, 2, v_inst_x27_2218_);
        v___x_2230_ = lean_apply_2(v_inst_2222_, lean_box(0), v___x_2229_);
        v___x_2231_ = lean_apply_4(
            v_toBind_2219_,
            lean_box(0),
            lean_box(0),
            v___x_2230_,
            v___f_2227_,
        );
        return v___x_2231_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(
    mut v_toPure_2241_: *mut LeanObject,
    mut v_inst_2242_: *mut LeanObject,
    mut v_toBind_2243_: *mut LeanObject,
    mut v___f_2244_: *mut LeanObject,
    mut v_inst_2245_: *mut LeanObject,
    mut v_ring_2246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intCastFn_x3f_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instType_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_intCastFn_x3f_2247_ = lean_ctor_get(v_ring_2246_, 11);
                if lean_obj_tag(v_intCastFn_x3f_2247_) == 1 {
                    lean_inc_ref(v_intCastFn_x3f_2247_);
                    lean_dec_ref(v_ring_2246_);
                    lean_dec(v_inst_2245_);
                    lean_dec(v___f_2244_);
                    lean_dec(v_toBind_2243_);
                    lean_dec_ref(v_inst_2242_);
                    v_val_2248_ = lean_ctor_get(v_intCastFn_x3f_2247_, 0);
                    lean_inc(v_val_2248_);
                    lean_dec_ref_known(v_intCastFn_x3f_2247_, 1);
                    v___x_2249_ = lean_apply_2(v_toPure_2241_, lean_box(0), v_val_2248_);
                    return v___x_2249_;
                } else {
                    v_type_2250_ = lean_ctor_get(v_ring_2246_, 1);
                    lean_inc_ref(v_type_2250_);
                    v_u_2251_ = lean_ctor_get(v_ring_2246_, 2);
                    lean_inc(v_u_2251_);
                    v_ringInst_2252_ = lean_ctor_get(v_ring_2246_, 3);
                    lean_inc_ref(v_ringInst_2252_);
                    lean_dec_ref(v_ring_2246_);
                    v_canonExpr_2253_ = lean_ctor_get(v_inst_2242_, 0);
                    v_synthInstance_x3f_2254_ = lean_ctor_get(v_inst_2242_, 1);
                    v_isSharedCheck_2275_ = (!lean_is_exclusive(v_inst_2242_)) as u8;
                    if v_isSharedCheck_2275_ == 0 {
                        v___x_2256_ = v_inst_2242_;
                        v_isShared_2257_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_synthInstance_x3f_2254_);
                        lean_inc(v_canonExpr_2253_);
                        lean_dec(v_inst_2242_);
                        v___x_2256_ = lean_box(0);
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
                v___x_2260_ = lean_box(0);
                if v_isShared_2257_ == 0 {
                    lean_ctor_set_tag(v___x_2256_, 1);
                    lean_ctor_set(v___x_2256_, 1, v___x_2260_);
                    lean_ctor_set(v___x_2256_, 0, v_u_2251_);
                    v___x_2262_ = v___x_2256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_u_2251_);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2260_);
                    v___x_2262_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v___x_2262_, 2);
                v___x_2263_ = l_Lean_mkConst(v___x_2259_, v___x_2262_);
                lean_inc_ref_n(v_type_2250_, 2);
                v_inst_x27_2264_ = l_Lean_mkAppB(v___x_2263_, v_type_2250_, v_ringInst_2252_);
                v___x_2265_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2;
                lean_inc_n(v_toBind_2243_, 2);
                v___f_2266_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3
                        as *mut core::ffi::c_void,
                    8,
                    7,
                );
                lean_closure_set(v___f_2266_, 0, v___x_2265_);
                lean_closure_set(v___f_2266_, 1, v___x_2258_);
                lean_closure_set(v___f_2266_, 2, v___x_2262_);
                lean_closure_set(v___f_2266_, 3, v_type_2250_);
                lean_closure_set(v___f_2266_, 4, v_canonExpr_2253_);
                lean_closure_set(v___f_2266_, 5, v_toBind_2243_);
                lean_closure_set(v___f_2266_, 6, v___f_2244_);
                v___f_2267_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2267_, 0, v___f_2266_);
                lean_inc_ref(v___f_2267_);
                v___f_2268_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                lean_closure_set(v___f_2268_, 0, v_toPure_2241_);
                lean_closure_set(v___f_2268_, 1, v_inst_x27_2264_);
                lean_closure_set(v___f_2268_, 2, v_toBind_2243_);
                lean_closure_set(v___f_2268_, 3, v___f_2267_);
                lean_closure_set(v___f_2268_, 4, v___f_2267_);
                lean_closure_set(v___f_2268_, 5, v_inst_2245_);
                v___x_2269_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3;
                v___x_2270_ = l_Lean_mkConst(v___x_2269_, v___x_2262_);
                v_instType_2271_ = l_Lean_Expr_app___override(v___x_2270_, v_type_2250_);
                v___x_2272_ = lean_apply_1(v_synthInstance_x3f_2254_, v_instType_2271_);
                v___x_2273_ = lean_apply_4(
                    v_toBind_2243_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_2276_: *mut LeanObject,
    mut v_inst_2277_: *mut LeanObject,
    mut v_inst_2278_: *mut LeanObject,
    mut v_inst_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2280_ = lean_ctor_get(v_inst_2277_, 0);
    lean_inc_ref(v_toApplicative_2280_);
    v_toBind_2281_ = lean_ctor_get(v_inst_2277_, 1);
    lean_inc_n(v_toBind_2281_, 3);
    lean_dec_ref(v_inst_2277_);
    v_getRing_2282_ = lean_ctor_get(v_inst_2279_, 0);
    lean_inc(v_getRing_2282_);
    v_modifyRing_2283_ = lean_ctor_get(v_inst_2279_, 1);
    lean_inc(v_modifyRing_2283_);
    lean_dec_ref(v_inst_2279_);
    v_toPure_2284_ = lean_ctor_get(v_toApplicative_2280_, 1);
    lean_inc_n(v_toPure_2284_, 2);
    lean_dec_ref(v_toApplicative_2280_);
    v___f_2285_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2285_, 0, v_toPure_2284_);
    lean_closure_set(v___f_2285_, 1, v_modifyRing_2283_);
    lean_closure_set(v___f_2285_, 2, v_toBind_2281_);
    v___f_2286_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2286_, 0, v_toPure_2284_);
    lean_closure_set(v___f_2286_, 1, v_inst_2278_);
    lean_closure_set(v___f_2286_, 2, v_toBind_2281_);
    lean_closure_set(v___f_2286_, 3, v___f_2285_);
    lean_closure_set(v___f_2286_, 4, v_inst_2276_);
    v___x_2287_ = lean_apply_4(
        v_toBind_2281_,
        lean_box(0),
        lean_box(0),
        v_getRing_2282_,
        v___f_2286_,
    );
    return v___x_2287_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(
    mut v_m_2288_: *mut LeanObject,
    mut v_inst_2289_: *mut LeanObject,
    mut v_inst_2290_: *mut LeanObject,
    mut v_inst_2291_: *mut LeanObject,
    mut v_inst_2292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(
        v_inst_2289_,
        v_inst_2290_,
        v_inst_2291_,
        v_inst_2292_,
    );
    return v___x_2293_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(
    mut v_natCastFn_2294_: *mut LeanObject,
    mut v_s_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_unused_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2296_ = lean_ctor_get(v_s_2295_, 0);
                v_type_2297_ = lean_ctor_get(v_s_2295_, 1);
                v_u_2298_ = lean_ctor_get(v_s_2295_, 2);
                v_ringInst_2299_ = lean_ctor_get(v_s_2295_, 3);
                v_semiringInst_2300_ = lean_ctor_get(v_s_2295_, 4);
                v_charInst_x3f_2301_ = lean_ctor_get(v_s_2295_, 5);
                v_addFn_x3f_2302_ = lean_ctor_get(v_s_2295_, 6);
                v_mulFn_x3f_2303_ = lean_ctor_get(v_s_2295_, 7);
                v_subFn_x3f_2304_ = lean_ctor_get(v_s_2295_, 8);
                v_negFn_x3f_2305_ = lean_ctor_get(v_s_2295_, 9);
                v_powFn_x3f_2306_ = lean_ctor_get(v_s_2295_, 10);
                v_intCastFn_x3f_2307_ = lean_ctor_get(v_s_2295_, 11);
                v_one_x3f_2308_ = lean_ctor_get(v_s_2295_, 13);
                v_vars_2309_ = lean_ctor_get(v_s_2295_, 14);
                v_varMap_2310_ = lean_ctor_get(v_s_2295_, 15);
                v_denote_2311_ = lean_ctor_get(v_s_2295_, 16);
                v_isSharedCheck_2319_ = (!lean_is_exclusive(v_s_2295_)) as u8;
                if v_isSharedCheck_2319_ == 0 {
                    v_unused_2320_ = lean_ctor_get(v_s_2295_, 12);
                    lean_dec(v_unused_2320_);
                    v___x_2313_ = v_s_2295_;
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_2311_);
                    lean_inc(v_varMap_2310_);
                    lean_inc(v_vars_2309_);
                    lean_inc(v_one_x3f_2308_);
                    lean_inc(v_intCastFn_x3f_2307_);
                    lean_inc(v_powFn_x3f_2306_);
                    lean_inc(v_negFn_x3f_2305_);
                    lean_inc(v_subFn_x3f_2304_);
                    lean_inc(v_mulFn_x3f_2303_);
                    lean_inc(v_addFn_x3f_2302_);
                    lean_inc(v_charInst_x3f_2301_);
                    lean_inc(v_semiringInst_2300_);
                    lean_inc(v_ringInst_2299_);
                    lean_inc(v_u_2298_);
                    lean_inc(v_type_2297_);
                    lean_inc(v_id_2296_);
                    lean_dec(v_s_2295_);
                    v___x_2313_ = lean_box(0);
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2315_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2315_, 0, v_natCastFn_2294_);
                if v_isShared_2314_ == 0 {
                    lean_ctor_set(v___x_2313_, 12, v___x_2315_);
                    v___x_2317_ = v___x_2313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_id_2296_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_type_2297_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_u_2298_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_ringInst_2299_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_semiringInst_2300_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 5, v_charInst_x3f_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 6, v_addFn_x3f_2302_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 7, v_mulFn_x3f_2303_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 8, v_subFn_x3f_2304_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 9, v_negFn_x3f_2305_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 10, v_powFn_x3f_2306_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 11, v_intCastFn_x3f_2307_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 12, v___x_2315_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 13, v_one_x3f_2308_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 14, v_vars_2309_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 15, v_varMap_2310_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 16, v_denote_2311_);
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
    mut v_toPure_2321_: *mut LeanObject,
    mut v_natCastFn_2322_: *mut LeanObject,
    mut v_____r_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    v___x_2324_ = lean_apply_2(v_toPure_2321_, lean_box(0), v_natCastFn_2322_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(
    mut v_toPure_2325_: *mut LeanObject,
    mut v_modifyRing_2326_: *mut LeanObject,
    mut v_toBind_2327_: *mut LeanObject,
    mut v_natCastFn_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_natCastFn_2328_);
    v___f_2329_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2329_, 0, v_natCastFn_2328_);
    v___f_2330_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2330_, 0, v_toPure_2325_);
    lean_closure_set(v___f_2330_, 1, v_natCastFn_2328_);
    v___x_2331_ = lean_apply_1(v_modifyRing_2326_, v___f_2329_);
    v___x_2332_ = lean_apply_4(
        v_toBind_2327_,
        lean_box(0),
        lean_box(0),
        v___x_2331_,
        v___f_2330_,
    );
    return v___x_2332_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(
    mut v_toPure_2333_: *mut LeanObject,
    mut v_inst_2334_: *mut LeanObject,
    mut v_inst_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
    mut v_toBind_2337_: *mut LeanObject,
    mut v___f_2338_: *mut LeanObject,
    mut v_ring_2339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natCastFn_x3f_2340_: *mut LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_2340_ = lean_ctor_get(v_ring_2339_, 12);
    if lean_obj_tag(v_natCastFn_x3f_2340_) == 1 {
        let mut v_val_2341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_natCastFn_x3f_2340_);
        lean_dec_ref(v_ring_2339_);
        lean_dec(v___f_2338_);
        lean_dec(v_toBind_2337_);
        lean_dec_ref(v_inst_2336_);
        lean_dec_ref(v_inst_2335_);
        lean_dec(v_inst_2334_);
        v_val_2341_ = lean_ctor_get(v_natCastFn_x3f_2340_, 0);
        lean_inc(v_val_2341_);
        lean_dec_ref_known(v_natCastFn_x3f_2340_, 1);
        v___x_2342_ = lean_apply_2(v_toPure_2333_, lean_box(0), v_val_2341_);
        return v___x_2342_;
    } else {
        let mut v_type_2343_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2344_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2333_);
        v_type_2343_ = lean_ctor_get(v_ring_2339_, 1);
        lean_inc_ref(v_type_2343_);
        v_u_2344_ = lean_ctor_get(v_ring_2339_, 2);
        lean_inc(v_u_2344_);
        v_semiringInst_2345_ = lean_ctor_get(v_ring_2339_, 4);
        lean_inc_ref(v_semiringInst_2345_);
        lean_dec_ref(v_ring_2339_);
        v___x_2346_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
            v_inst_2334_,
            v_inst_2335_,
            v_inst_2336_,
            v_u_2344_,
            v_type_2343_,
            v_semiringInst_2345_,
        );
        v___x_2347_ = lean_apply_4(
            v_toBind_2337_,
            lean_box(0),
            lean_box(0),
            v___x_2346_,
            v___f_2338_,
        );
        return v___x_2347_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
    mut v_inst_2348_: *mut LeanObject,
    mut v_inst_2349_: *mut LeanObject,
    mut v_inst_2350_: *mut LeanObject,
    mut v_inst_2351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2352_ = lean_ctor_get(v_inst_2349_, 0);
    v_toBind_2353_ = lean_ctor_get(v_inst_2349_, 1);
    lean_inc_n(v_toBind_2353_, 3);
    v_getRing_2354_ = lean_ctor_get(v_inst_2351_, 0);
    lean_inc(v_getRing_2354_);
    v_modifyRing_2355_ = lean_ctor_get(v_inst_2351_, 1);
    lean_inc(v_modifyRing_2355_);
    lean_dec_ref(v_inst_2351_);
    v_toPure_2356_ = lean_ctor_get(v_toApplicative_2352_, 1);
    lean_inc_n(v_toPure_2356_, 2);
    v___f_2357_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2357_, 0, v_toPure_2356_);
    lean_closure_set(v___f_2357_, 1, v_modifyRing_2355_);
    lean_closure_set(v___f_2357_, 2, v_toBind_2353_);
    v___f_2358_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2358_, 0, v_toPure_2356_);
    lean_closure_set(v___f_2358_, 1, v_inst_2348_);
    lean_closure_set(v___f_2358_, 2, v_inst_2349_);
    lean_closure_set(v___f_2358_, 3, v_inst_2350_);
    lean_closure_set(v___f_2358_, 4, v_toBind_2353_);
    lean_closure_set(v___f_2358_, 5, v___f_2357_);
    v___x_2359_ = lean_apply_4(
        v_toBind_2353_,
        lean_box(0),
        lean_box(0),
        v_getRing_2354_,
        v___f_2358_,
    );
    return v___x_2359_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(
    mut v_m_2360_: *mut LeanObject,
    mut v_inst_2361_: *mut LeanObject,
    mut v_inst_2362_: *mut LeanObject,
    mut v_inst_2363_: *mut LeanObject,
    mut v_inst_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    v___x_2365_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
        v_inst_2361_,
        v_inst_2362_,
        v_inst_2363_,
        v_inst_2364_,
    );
    return v___x_2365_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2367_: *mut LeanObject = core::ptr::null_mut();
    v___x_2366_ = lean_unsigned_to_nat(1);
    v_n_2367_ = l_Lean_mkRawNatLit(v___x_2366_);
    return v_n_2367_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(
    mut v_inst_2378_: *mut LeanObject,
    mut v_u_2379_: *mut LeanObject,
    mut v_type_2380_: *mut LeanObject,
    mut v_semiringInst_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonExpr_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v_n_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNatInst_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v_unused_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_canonExpr_2382_ = lean_ctor_get(v_inst_2378_, 0);
                v_isSharedCheck_2398_ = (!lean_is_exclusive(v_inst_2378_)) as u8;
                if v_isSharedCheck_2398_ == 0 {
                    v_unused_2399_ = lean_ctor_get(v_inst_2378_, 1);
                    lean_dec(v_unused_2399_);
                    v___x_2384_ = v_inst_2378_;
                    v_isShared_2385_ = v_isSharedCheck_2398_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canonExpr_2382_);
                    lean_dec(v_inst_2378_);
                    v___x_2384_ = lean_box(0);
                    v_isShared_2385_ = v_isSharedCheck_2398_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_n_2386_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
                v___x_2387_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2;
                v___x_2388_ = lean_box(0);
                if v_isShared_2385_ == 0 {
                    lean_ctor_set_tag(v___x_2384_, 1);
                    lean_ctor_set(v___x_2384_, 1, v___x_2388_);
                    lean_ctor_set(v___x_2384_, 0, v_u_2379_);
                    v___x_2390_ = v___x_2384_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_u_2379_);
                    lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2388_);
                    v___x_2390_ = v_reuseFailAlloc_2397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_2390_);
                v___x_2391_ = l_Lean_mkConst(v___x_2387_, v___x_2390_);
                lean_inc_ref(v_type_2380_);
                v_ofNatInst_2392_ =
                    l_Lean_mkApp3(v___x_2391_, v_type_2380_, v_semiringInst_2381_, v_n_2386_);
                v___x_2393_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4;
                v___x_2394_ = l_Lean_mkConst(v___x_2393_, v___x_2390_);
                v___x_2395_ =
                    l_Lean_mkApp3(v___x_2394_, v_type_2380_, v_n_2386_, v_ofNatInst_2392_);
                v___x_2396_ = lean_apply_1(v_canonExpr_2382_, v___x_2395_);
                return v___x_2396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne(
    mut v_m_2400_: *mut LeanObject,
    mut v_inst_2401_: *mut LeanObject,
    mut v_u_2402_: *mut LeanObject,
    mut v_type_2403_: *mut LeanObject,
    mut v_semiringInst_2404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    v___x_2405_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_2401_, v_u_2402_, v_type_2403_, v_semiringInst_2404_);
    return v___x_2405_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0(
    mut v_one_2406_: *mut LeanObject,
    mut v_s_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denote_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut v_unused_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2408_ = lean_ctor_get(v_s_2407_, 0);
                v_type_2409_ = lean_ctor_get(v_s_2407_, 1);
                v_u_2410_ = lean_ctor_get(v_s_2407_, 2);
                v_ringInst_2411_ = lean_ctor_get(v_s_2407_, 3);
                v_semiringInst_2412_ = lean_ctor_get(v_s_2407_, 4);
                v_charInst_x3f_2413_ = lean_ctor_get(v_s_2407_, 5);
                v_addFn_x3f_2414_ = lean_ctor_get(v_s_2407_, 6);
                v_mulFn_x3f_2415_ = lean_ctor_get(v_s_2407_, 7);
                v_subFn_x3f_2416_ = lean_ctor_get(v_s_2407_, 8);
                v_negFn_x3f_2417_ = lean_ctor_get(v_s_2407_, 9);
                v_powFn_x3f_2418_ = lean_ctor_get(v_s_2407_, 10);
                v_intCastFn_x3f_2419_ = lean_ctor_get(v_s_2407_, 11);
                v_natCastFn_x3f_2420_ = lean_ctor_get(v_s_2407_, 12);
                v_vars_2421_ = lean_ctor_get(v_s_2407_, 14);
                v_varMap_2422_ = lean_ctor_get(v_s_2407_, 15);
                v_denote_2423_ = lean_ctor_get(v_s_2407_, 16);
                v_isSharedCheck_2431_ = (!lean_is_exclusive(v_s_2407_)) as u8;
                if v_isSharedCheck_2431_ == 0 {
                    v_unused_2432_ = lean_ctor_get(v_s_2407_, 13);
                    lean_dec(v_unused_2432_);
                    v___x_2425_ = v_s_2407_;
                    v_isShared_2426_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_denote_2423_);
                    lean_inc(v_varMap_2422_);
                    lean_inc(v_vars_2421_);
                    lean_inc(v_natCastFn_x3f_2420_);
                    lean_inc(v_intCastFn_x3f_2419_);
                    lean_inc(v_powFn_x3f_2418_);
                    lean_inc(v_negFn_x3f_2417_);
                    lean_inc(v_subFn_x3f_2416_);
                    lean_inc(v_mulFn_x3f_2415_);
                    lean_inc(v_addFn_x3f_2414_);
                    lean_inc(v_charInst_x3f_2413_);
                    lean_inc(v_semiringInst_2412_);
                    lean_inc(v_ringInst_2411_);
                    lean_inc(v_u_2410_);
                    lean_inc(v_type_2409_);
                    lean_inc(v_id_2408_);
                    lean_dec(v_s_2407_);
                    v___x_2425_ = lean_box(0);
                    v_isShared_2426_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2427_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2427_, 0, v_one_2406_);
                if v_isShared_2426_ == 0 {
                    lean_ctor_set(v___x_2425_, 13, v___x_2427_);
                    v___x_2429_ = v___x_2425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 17, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_id_2408_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_type_2409_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_u_2410_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_ringInst_2411_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 4, v_semiringInst_2412_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 5, v_charInst_x3f_2413_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 6, v_addFn_x3f_2414_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 7, v_mulFn_x3f_2415_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 8, v_subFn_x3f_2416_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 9, v_negFn_x3f_2417_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 10, v_powFn_x3f_2418_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 11, v_intCastFn_x3f_2419_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 12, v_natCastFn_x3f_2420_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 13, v___x_2427_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 14, v_vars_2421_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 15, v_varMap_2422_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 16, v_denote_2423_);
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
    mut v_toPure_2433_: *mut LeanObject,
    mut v_one_2434_: *mut LeanObject,
    mut v_____r_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    v___x_2436_ = lean_apply_2(v_toPure_2433_, lean_box(0), v_one_2434_);
    return v___x_2436_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(
    mut v_one_2437_: *mut LeanObject,
    mut v_inst_2438_: *mut LeanObject,
    mut v_toBind_2439_: *mut LeanObject,
    mut v___f_2440_: *mut LeanObject,
    mut v_____r_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    v___x_2442_ = lean_unsigned_to_nat(0);
    v___x_2443_ = lean_box(0);
    v___x_2444_ = lean_alloc_closure(
        l_Lean_Meta_Grind_internalize___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    lean_closure_set(v___x_2444_, 0, v_one_2437_);
    lean_closure_set(v___x_2444_, 1, v___x_2442_);
    lean_closure_set(v___x_2444_, 2, v___x_2443_);
    v___x_2445_ = lean_apply_2(v_inst_2438_, lean_box(0), v___x_2444_);
    v___x_2446_ = lean_apply_4(
        v_toBind_2439_,
        lean_box(0),
        lean_box(0),
        v___x_2445_,
        v___f_2440_,
    );
    return v___x_2446_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(
    mut v_toPure_2447_: *mut LeanObject,
    mut v_inst_2448_: *mut LeanObject,
    mut v_toBind_2449_: *mut LeanObject,
    mut v_modifyRing_2450_: *mut LeanObject,
    mut v_one_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_one_2451_, 2);
    v___f_2452_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2452_, 0, v_one_2451_);
    v___f_2453_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2453_, 0, v_toPure_2447_);
    lean_closure_set(v___f_2453_, 1, v_one_2451_);
    lean_inc(v_toBind_2449_);
    v___f_2454_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2454_, 0, v_one_2451_);
    lean_closure_set(v___f_2454_, 1, v_inst_2448_);
    lean_closure_set(v___f_2454_, 2, v_toBind_2449_);
    lean_closure_set(v___f_2454_, 3, v___f_2453_);
    v___x_2455_ = lean_apply_1(v_modifyRing_2450_, v___f_2452_);
    v___x_2456_ = lean_apply_4(
        v_toBind_2449_,
        lean_box(0),
        lean_box(0),
        v___x_2455_,
        v___f_2454_,
    );
    return v___x_2456_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(
    mut v_toPure_2457_: *mut LeanObject,
    mut v_inst_2458_: *mut LeanObject,
    mut v_toBind_2459_: *mut LeanObject,
    mut v___f_2460_: *mut LeanObject,
    mut v_ring_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_one_x3f_2462_: *mut LeanObject = core::ptr::null_mut();
    v_one_x3f_2462_ = lean_ctor_get(v_ring_2461_, 13);
    if lean_obj_tag(v_one_x3f_2462_) == 1 {
        let mut v_val_2463_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_one_x3f_2462_);
        lean_dec_ref(v_ring_2461_);
        lean_dec(v___f_2460_);
        lean_dec(v_toBind_2459_);
        lean_dec_ref(v_inst_2458_);
        v_val_2463_ = lean_ctor_get(v_one_x3f_2462_, 0);
        lean_inc(v_val_2463_);
        lean_dec_ref_known(v_one_x3f_2462_, 1);
        v___x_2464_ = lean_apply_2(v_toPure_2457_, lean_box(0), v_val_2463_);
        return v___x_2464_;
    } else {
        let mut v_type_2465_: *mut LeanObject = core::ptr::null_mut();
        let mut v_u_2466_: *mut LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2457_);
        v_type_2465_ = lean_ctor_get(v_ring_2461_, 1);
        lean_inc_ref(v_type_2465_);
        v_u_2466_ = lean_ctor_get(v_ring_2461_, 2);
        lean_inc(v_u_2466_);
        v_semiringInst_2467_ = lean_ctor_get(v_ring_2461_, 4);
        lean_inc_ref(v_semiringInst_2467_);
        lean_dec_ref(v_ring_2461_);
        v___x_2468_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_2458_, v_u_2466_, v_type_2465_, v_semiringInst_2467_);
        v___x_2469_ = lean_apply_4(
            v_toBind_2459_,
            lean_box(0),
            lean_box(0),
            v___x_2468_,
            v___f_2460_,
        );
        return v___x_2469_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(
    mut v_inst_2470_: *mut LeanObject,
    mut v_inst_2471_: *mut LeanObject,
    mut v_inst_2472_: *mut LeanObject,
    mut v_inst_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getRing_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2474_ = lean_ctor_get(v_inst_2470_, 0);
    lean_inc_ref(v_toApplicative_2474_);
    v_toBind_2475_ = lean_ctor_get(v_inst_2470_, 1);
    lean_inc_n(v_toBind_2475_, 3);
    lean_dec_ref(v_inst_2470_);
    v_getRing_2476_ = lean_ctor_get(v_inst_2472_, 0);
    lean_inc(v_getRing_2476_);
    v_modifyRing_2477_ = lean_ctor_get(v_inst_2472_, 1);
    lean_inc(v_modifyRing_2477_);
    lean_dec_ref(v_inst_2472_);
    v_toPure_2478_ = lean_ctor_get(v_toApplicative_2474_, 1);
    lean_inc_n(v_toPure_2478_, 2);
    lean_dec_ref(v_toApplicative_2474_);
    v___f_2479_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2479_, 0, v_toPure_2478_);
    lean_closure_set(v___f_2479_, 1, v_inst_2473_);
    lean_closure_set(v___f_2479_, 2, v_toBind_2475_);
    lean_closure_set(v___f_2479_, 3, v_modifyRing_2477_);
    v___f_2480_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2480_, 0, v_toPure_2478_);
    lean_closure_set(v___f_2480_, 1, v_inst_2471_);
    lean_closure_set(v___f_2480_, 2, v_toBind_2475_);
    lean_closure_set(v___f_2480_, 3, v___f_2479_);
    v___x_2481_ = lean_apply_4(
        v_toBind_2475_,
        lean_box(0),
        lean_box(0),
        v_getRing_2476_,
        v___f_2480_,
    );
    return v___x_2481_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne(
    mut v_m_2482_: *mut LeanObject,
    mut v_inst_2483_: *mut LeanObject,
    mut v_inst_2484_: *mut LeanObject,
    mut v_inst_2485_: *mut LeanObject,
    mut v_inst_2486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    v___x_2487_ = l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(
        v_inst_2483_,
        v_inst_2484_,
        v_inst_2485_,
        v_inst_2486_,
    );
    return v___x_2487_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0(
    mut v_invFn_2488_: *mut LeanObject,
    mut v_s_2489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toRing_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_steps_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recheck_2503_: u8 = 0;
    let mut v_invSet_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2507_: u8 = 0;
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v_unused_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2490_ = lean_ctor_get(v_s_2489_, 0);
                v_semiringId_x3f_2491_ = lean_ctor_get(v_s_2489_, 2);
                v_commSemiringInst_2492_ = lean_ctor_get(v_s_2489_, 3);
                v_commRingInst_2493_ = lean_ctor_get(v_s_2489_, 4);
                v_noZeroDivInst_x3f_2494_ = lean_ctor_get(v_s_2489_, 5);
                v_fieldInst_x3f_2495_ = lean_ctor_get(v_s_2489_, 6);
                v_powIdentityInst_x3f_2496_ = lean_ctor_get(v_s_2489_, 7);
                v_denoteEntries_2497_ = lean_ctor_get(v_s_2489_, 8);
                v_nextId_2498_ = lean_ctor_get(v_s_2489_, 9);
                v_steps_2499_ = lean_ctor_get(v_s_2489_, 10);
                v_queue_2500_ = lean_ctor_get(v_s_2489_, 11);
                v_basis_2501_ = lean_ctor_get(v_s_2489_, 12);
                v_diseqs_2502_ = lean_ctor_get(v_s_2489_, 13);
                v_recheck_2503_ = lean_ctor_get_uint8(
                    v_s_2489_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_invSet_2504_ = lean_ctor_get(v_s_2489_, 14);
                v_powIdentityVarCount_2505_ = lean_ctor_get(v_s_2489_, 15);
                v_numEq0_x3f_2506_ = lean_ctor_get(v_s_2489_, 16);
                v_numEq0Updated_2507_ = lean_ctor_get_uint8(
                    v_s_2489_,
                    (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2515_ = (!lean_is_exclusive(v_s_2489_)) as u8;
                if v_isSharedCheck_2515_ == 0 {
                    v_unused_2516_ = lean_ctor_get(v_s_2489_, 1);
                    lean_dec(v_unused_2516_);
                    v___x_2509_ = v_s_2489_;
                    v_isShared_2510_ = v_isSharedCheck_2515_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_numEq0_x3f_2506_);
                    lean_inc(v_powIdentityVarCount_2505_);
                    lean_inc(v_invSet_2504_);
                    lean_inc(v_diseqs_2502_);
                    lean_inc(v_basis_2501_);
                    lean_inc(v_queue_2500_);
                    lean_inc(v_steps_2499_);
                    lean_inc(v_nextId_2498_);
                    lean_inc(v_denoteEntries_2497_);
                    lean_inc(v_powIdentityInst_x3f_2496_);
                    lean_inc(v_fieldInst_x3f_2495_);
                    lean_inc(v_noZeroDivInst_x3f_2494_);
                    lean_inc(v_commRingInst_2493_);
                    lean_inc(v_commSemiringInst_2492_);
                    lean_inc(v_semiringId_x3f_2491_);
                    lean_inc(v_toRing_2490_);
                    lean_dec(v_s_2489_);
                    v___x_2509_ = lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2511_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2511_, 0, v_invFn_2488_);
                if v_isShared_2510_ == 0 {
                    lean_ctor_set(v___x_2509_, 1, v___x_2511_);
                    v___x_2513_ = v___x_2509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 17, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_toRing_2490_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2511_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_semiringId_x3f_2491_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_commSemiringInst_2492_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_commRingInst_2493_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 5, v_noZeroDivInst_x3f_2494_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 6, v_fieldInst_x3f_2495_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 7, v_powIdentityInst_x3f_2496_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 8, v_denoteEntries_2497_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 9, v_nextId_2498_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 10, v_steps_2499_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 11, v_queue_2500_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 12, v_basis_2501_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 13, v_diseqs_2502_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 14, v_invSet_2504_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 15, v_powIdentityVarCount_2505_);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 16, v_numEq0_x3f_2506_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2514_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_recheck_2503_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2514_,
                        (core::mem::size_of::<*mut LeanObject>() * 17 + 1) as u32,
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
    mut v_toPure_2517_: *mut LeanObject,
    mut v_invFn_2518_: *mut LeanObject,
    mut v_____r_2519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    v___x_2520_ = lean_apply_2(v_toPure_2517_, lean_box(0), v_invFn_2518_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2(
    mut v_toPure_2521_: *mut LeanObject,
    mut v_modifyCommRing_2522_: *mut LeanObject,
    mut v_toBind_2523_: *mut LeanObject,
    mut v_invFn_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_invFn_2524_);
    v___f_2525_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2525_, 0, v_invFn_2524_);
    v___f_2526_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2526_, 0, v_toPure_2521_);
    lean_closure_set(v___f_2526_, 1, v_invFn_2524_);
    v___x_2527_ = lean_apply_1(v_modifyCommRing_2522_, v___f_2525_);
    v___x_2528_ = lean_apply_4(
        v_toBind_2523_,
        lean_box(0),
        lean_box(0),
        v___x_2527_,
        v___f_2526_,
    );
    return v___x_2528_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8()
-> *mut LeanObject {
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    v___x_2544_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7;
    v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
    return v___x_2545_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(
    mut v_toPure_2546_: *mut LeanObject,
    mut v_inst_2547_: *mut LeanObject,
    mut v_inst_2548_: *mut LeanObject,
    mut v_inst_2549_: *mut LeanObject,
    mut v_inst_2550_: *mut LeanObject,
    mut v_toBind_2551_: *mut LeanObject,
    mut v___f_2552_: *mut LeanObject,
    mut v_ring_2553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fieldInst_x3f_2554_: *mut LeanObject = core::ptr::null_mut();
    v_fieldInst_x3f_2554_ = lean_ctor_get(v_ring_2553_, 6);
    if lean_obj_tag(v_fieldInst_x3f_2554_) == 1 {
        let mut v_invFn_x3f_2555_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_fieldInst_x3f_2554_);
        v_invFn_x3f_2555_ = lean_ctor_get(v_ring_2553_, 1);
        if lean_obj_tag(v_invFn_x3f_2555_) == 1 {
            let mut v_val_2556_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_invFn_x3f_2555_);
            lean_dec_ref_known(v_fieldInst_x3f_2554_, 1);
            lean_dec_ref(v_ring_2553_);
            lean_dec(v___f_2552_);
            lean_dec(v_toBind_2551_);
            lean_dec_ref(v_inst_2550_);
            lean_dec_ref(v_inst_2549_);
            lean_dec_ref(v_inst_2548_);
            lean_dec(v_inst_2547_);
            v_val_2556_ = lean_ctor_get(v_invFn_x3f_2555_, 0);
            lean_inc(v_val_2556_);
            lean_dec_ref_known(v_invFn_x3f_2555_, 1);
            v___x_2557_ = lean_apply_2(v_toPure_2546_, lean_box(0), v_val_2556_);
            return v___x_2557_;
        } else {
            let mut v_toRing_2558_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_2559_: *mut LeanObject = core::ptr::null_mut();
            let mut v_type_2560_: *mut LeanObject = core::ptr::null_mut();
            let mut v_u_2561_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expectedInst_2566_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_2546_);
            v_toRing_2558_ = lean_ctor_get(v_ring_2553_, 0);
            lean_inc_ref(v_toRing_2558_);
            lean_dec_ref(v_ring_2553_);
            v_val_2559_ = lean_ctor_get(v_fieldInst_x3f_2554_, 0);
            lean_inc(v_val_2559_);
            lean_dec_ref_known(v_fieldInst_x3f_2554_, 1);
            v_type_2560_ = lean_ctor_get(v_toRing_2558_, 1);
            lean_inc_ref_n(v_type_2560_, 2);
            v_u_2561_ = lean_ctor_get(v_toRing_2558_, 2);
            lean_inc_n(v_u_2561_, 2);
            lean_dec_ref(v_toRing_2558_);
            v___x_2562_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2;
            v___x_2563_ = lean_box(0);
            v___x_2564_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2564_, 0, v_u_2561_);
            lean_ctor_set(v___x_2564_, 1, v___x_2563_);
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
            v___x_2570_ = lean_apply_4(
                v_toBind_2551_,
                lean_box(0),
                lean_box(0),
                v___x_2569_,
                v___f_2552_,
            );
            return v___x_2570_;
        }
    } else {
        let mut v_toRing_2571_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_2572_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2552_);
        lean_dec(v_toBind_2551_);
        lean_dec_ref(v_inst_2550_);
        lean_dec(v_inst_2547_);
        lean_dec(v_toPure_2546_);
        v_toRing_2571_ = lean_ctor_get(v_ring_2553_, 0);
        lean_inc_ref(v_toRing_2571_);
        lean_dec_ref(v_ring_2553_);
        v_type_2572_ = lean_ctor_get(v_toRing_2571_, 1);
        lean_inc_ref(v_type_2572_);
        lean_dec_ref(v_toRing_2571_);
        v___x_2573_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once
            ),
            _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8,
        );
        v___x_2574_ = l_Lean_indentExpr(v_type_2572_);
        v___x_2575_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2575_, 0, v___x_2573_);
        lean_ctor_set(v___x_2575_, 1, v___x_2574_);
        v___x_2576_ = l_Lean_throwError___redArg(v_inst_2549_, v_inst_2548_, v___x_2575_);
        return v___x_2576_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(
    mut v_inst_2577_: *mut LeanObject,
    mut v_inst_2578_: *mut LeanObject,
    mut v_inst_2579_: *mut LeanObject,
    mut v_inst_2580_: *mut LeanObject,
    mut v_inst_2581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2582_ = lean_ctor_get(v_inst_2579_, 0);
    v_toBind_2583_ = lean_ctor_get(v_inst_2579_, 1);
    lean_inc_n(v_toBind_2583_, 3);
    v_getCommRing_2584_ = lean_ctor_get(v_inst_2581_, 0);
    lean_inc(v_getCommRing_2584_);
    v_modifyCommRing_2585_ = lean_ctor_get(v_inst_2581_, 1);
    lean_inc(v_modifyCommRing_2585_);
    lean_dec_ref(v_inst_2581_);
    v_toPure_2586_ = lean_ctor_get(v_toApplicative_2582_, 1);
    lean_inc_n(v_toPure_2586_, 2);
    v___f_2587_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2587_, 0, v_toPure_2586_);
    lean_closure_set(v___f_2587_, 1, v_modifyCommRing_2585_);
    lean_closure_set(v___f_2587_, 2, v_toBind_2583_);
    v___f_2588_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2588_, 0, v_toPure_2586_);
    lean_closure_set(v___f_2588_, 1, v_inst_2577_);
    lean_closure_set(v___f_2588_, 2, v_inst_2578_);
    lean_closure_set(v___f_2588_, 3, v_inst_2579_);
    lean_closure_set(v___f_2588_, 4, v_inst_2580_);
    lean_closure_set(v___f_2588_, 5, v_toBind_2583_);
    lean_closure_set(v___f_2588_, 6, v___f_2587_);
    v___x_2589_ = lean_apply_4(
        v_toBind_2583_,
        lean_box(0),
        lean_box(0),
        v_getCommRing_2584_,
        v___f_2588_,
    );
    return v___x_2589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn(
    mut v_m_2590_: *mut LeanObject,
    mut v_inst_2591_: *mut LeanObject,
    mut v_inst_2592_: *mut LeanObject,
    mut v_inst_2593_: *mut LeanObject,
    mut v_inst_2594_: *mut LeanObject,
    mut v_inst_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
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
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
}
