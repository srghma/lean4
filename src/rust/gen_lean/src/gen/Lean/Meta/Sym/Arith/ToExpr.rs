// Lean compiler output
// Module: Lean.Meta.Sym.Arith.ToExpr
// Imports: Init.Grind.Ring.CommSemiringAdapter Lean.ToExpr
use crate::ffi::{lean_int_dec_le, lean_int_neg, lean_nat_to_int};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Grind::Ring::CommSemiringAdapter::{
    initialize_Init_Grind_Ring_CommSemiringAdapter,
    runtime_initialize_Init_Grind_Ring_CommSemiringAdapter,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_mkApp3, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::ToExpr::{
    initialize_Lean_ToExpr, l_Lean_instToExprInt_mkNat, runtime_initialize_Lean_ToExpr,
};
pub static l_Lean_Meta_Sym_Arith_ofPower___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofPower___closed__1_value: leanh::LeanStringObject<6> =
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
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofPower___closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofPower___closed__3_value: leanh::LeanStringObject<6> =
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
        m_data: [80, 111, 119, 101, 114, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofPower___closed__4_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [109, 107, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__3_value)
                as *mut leanh::LeanObject,
            152760725783678224 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofPower___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__4_value)
                as *mut leanh::LeanObject,
            9938267393800656552 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPower___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_instToExprPower___closed__0_value:
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
    m_fun: l_Lean_Meta_Sym_Arith_ofPower as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Arith_instToExprPower___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
            as *mut leanh::LeanObject,
        16367934121419604941 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__3_value)
            as *mut leanh::LeanObject,
        152760725783678224 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Arith_instToExprPower___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_instToExprPower___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprPower___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instToExprPower___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprPower___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instToExprPower: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofMon___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [77, 111, 110, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofMon___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [117, 110, 105, 116, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__0_value)
                as *mut leanh::LeanObject,
            16953917829499197705 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofMon___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__1_value)
                as *mut leanh::LeanObject,
            18375699169416510308 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofMon___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [109, 117, 108, 116, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__0_value)
                as *mut leanh::LeanObject,
            16953917829499197705 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofMon___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__4_value)
                as *mut leanh::LeanObject,
            1260410007619339063 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofMon___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_instToExprMon___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_Sym_Arith_ofMon as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Arith_instToExprMon___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
            as *mut leanh::LeanObject,
        16367934121419604941 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofMon___closed__0_value)
                as *mut leanh::LeanObject,
            16953917829499197705 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_instToExprMon___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_instToExprMon___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprMon___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instToExprMon___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprMon___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instToExprMon: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [80, 111, 108, 121, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value: leanh::LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value)
                as *mut leanh::LeanObject,
            1541904202362099191 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value)
                as *mut leanh::LeanObject,
            17643851365657578359 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value: leanh::LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__6_value: leanh::LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofPoly___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value)
                as *mut leanh::LeanObject,
            9626815015619986526 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__6_value)
                as *mut leanh::LeanObject,
            17185717442815859305 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__11_value: leanh::LeanStringObject<4> =
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
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__11_value)
                as *mut leanh::LeanObject,
            7009148538150066493 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__14_value: leanh::LeanStringObject<11> =
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
        m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofPoly___closed__15_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__11_value)
                as *mut leanh::LeanObject,
            7009148538150066493 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__15_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__15_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__14_value)
                as *mut leanh::LeanObject,
            6362876895233142233 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__17_value: leanh::LeanStringObject<4> =
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
        m_data: [97, 100, 100, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__17_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value)
                as *mut leanh::LeanObject,
            1541904202362099191 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__17_value)
                as *mut leanh::LeanObject,
            2209249661734524766 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofPoly___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_Sym_Arith_ofPoly as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
            as *mut leanh::LeanObject,
        16367934121419604941 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value)
                as *mut leanh::LeanObject,
            1541904202362099191 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instToExprPoly: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [69, 120, 112, 114, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value)
                as *mut leanh::LeanObject,
            14108921569236860515 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
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
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3_value)
                as *mut leanh::LeanObject,
            4973144201412494589 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
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
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6_value)
                as *mut leanh::LeanObject,
            17555198233385870698 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9_value: leanh::LeanStringObject<4> =
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
        m_data: [118, 97, 114, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9_value)
                as *mut leanh::LeanObject,
            2418133369870432750 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__6_value)
                as *mut leanh::LeanObject,
            5872354066780731488 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPoly___closed__17_value)
                as *mut leanh::LeanObject,
            8630942631786967538 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16_value: leanh::LeanStringObject<4> =
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
        m_data: [115, 117, 98, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16_value)
                as *mut leanh::LeanObject,
            4776573289065043689 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19_value: leanh::LeanStringObject<4> =
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
        m_data: [109, 117, 108, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19_value)
                as *mut leanh::LeanObject,
            1701784974265380764 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22_value: leanh::LeanStringObject<4> =
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
        m_data: [112, 111, 119, 0],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
                as *mut leanh::LeanObject,
            16367934121419604941 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22_value)
                as *mut leanh::LeanObject,
            16509265838784706939 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_Sym_Arith_ofRingExpr as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofPower___closed__2_value)
            as *mut leanh::LeanObject,
        16367934121419604941 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value)
                as *mut leanh::LeanObject,
            1563393096373910075 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Sym_Arith_instToExprExpr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPower___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = leanh::lean_box(0);
    v___x_355_ = l_Lean_Meta_Sym_Arith_ofPower___closed__5;
    v___x_356_ = l_Lean_mkConst(v___x_355_, v___x_354_);
    return v___x_356_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ofPower(
    mut v_p_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_358_ = leanh::lean_ctor_get(v_p_357_, 0);
    leanh::lean_inc(v_x_358_);
    v_k_359_ = leanh::lean_ctor_get(v_p_357_, 1);
    leanh::lean_inc(v_k_359_);
    leanh::lean_dec_ref(v_p_357_);
    v___x_360_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPower___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPower___closed__6_once),
        _init_l_Lean_Meta_Sym_Arith_ofPower___closed__6,
    );
    v___x_361_ = l_Lean_mkNatLit(v_x_358_);
    v___x_362_ = l_Lean_mkNatLit(v_k_359_);
    v___x_363_ = l_Lean_mkAppB(v___x_360_, v___x_361_, v___x_362_);
    return v___x_363_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_370_ = leanh::lean_box(0);
    v___x_371_ = l_Lean_Meta_Sym_Arith_instToExprPower___closed__1;
    v___x_372_ = l_Lean_mkConst(v___x_371_, v___x_370_);
    return v___x_372_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__2_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__2,
    );
    v___x_374_ = l_Lean_Meta_Sym_Arith_instToExprPower___closed__0;
    v___x_375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_375_, 0, v___x_374_);
    leanh::lean_ctor_set(v___x_375_, 1, v___x_373_);
    return v___x_375_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprPower() -> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPower___closed__3_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__3,
    );
    return v___x_376_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofMon___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = leanh::lean_box(0);
    v___x_386_ = l_Lean_Meta_Sym_Arith_ofMon___closed__2;
    v___x_387_ = l_Lean_mkConst(v___x_386_, v___x_385_);
    return v___x_387_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofMon___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = leanh::lean_box(0);
    v___x_396_ = l_Lean_Meta_Sym_Arith_ofMon___closed__5;
    v___x_397_ = l_Lean_mkConst(v___x_396_, v___x_395_);
    return v___x_397_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ofMon(
    mut v_m_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_m_398_) == 0 {
        let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_399_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofMon___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofMon___closed__3_once),
            _init_l_Lean_Meta_Sym_Arith_ofMon___closed__3,
        );
        return v___x_399_;
    } else {
        let mut v_p_400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_p_400_ = leanh::lean_ctor_get(v_m_398_, 0);
        leanh::lean_inc_ref(v_p_400_);
        v_m_401_ = leanh::lean_ctor_get(v_m_398_, 1);
        leanh::lean_inc(v_m_401_);
        leanh::lean_dec_ref_known(v_m_398_, 2);
        v___x_402_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofMon___closed__6),
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofMon___closed__6_once),
            _init_l_Lean_Meta_Sym_Arith_ofMon___closed__6,
        );
        v___x_403_ = l_Lean_Meta_Sym_Arith_ofPower(v_p_400_);
        v___x_404_ = l_Lean_Meta_Sym_Arith_ofMon(v_m_401_);
        v___x_405_ = l_Lean_mkAppB(v___x_402_, v___x_403_, v___x_404_);
        return v___x_405_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_412_ = leanh::lean_box(0);
    v___x_413_ = l_Lean_Meta_Sym_Arith_instToExprMon___closed__1;
    v___x_414_ = l_Lean_mkConst(v___x_413_, v___x_412_);
    return v___x_414_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__2_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__2,
    );
    v___x_416_ = l_Lean_Meta_Sym_Arith_instToExprMon___closed__0;
    v___x_417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_417_, 0, v___x_416_);
    leanh::lean_ctor_set(v___x_417_, 1, v___x_415_);
    return v___x_417_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprMon() -> *mut leanh::LeanObject {
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprMon___closed__3_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__3,
    );
    return v___x_418_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = leanh::lean_box(0);
    v___x_428_ = l_Lean_Meta_Sym_Arith_ofPoly___closed__2;
    v___x_429_ = l_Lean_mkConst(v___x_428_, v___x_427_);
    return v___x_429_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = leanh::lean_unsigned_to_nat(0);
    v___x_431_ = lean_nat_to_int(v___x_430_);
    return v___x_431_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ = leanh::lean_unsigned_to_nat(0);
    v___x_438_ = l_Lean_Level_ofNat(v___x_437_);
    return v___x_438_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = leanh::lean_box(0);
    v___x_440_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__8_once),
        _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__8,
    );
    v___x_441_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
    leanh::lean_ctor_set(v___x_441_, 1, v___x_439_);
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__9_once),
        _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__9,
    );
    v___x_443_ = l_Lean_Meta_Sym_Arith_ofPoly___closed__7;
    v___x_444_ = l_Lean_Expr_const___override(v___x_443_, v___x_442_);
    return v___x_444_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ = leanh::lean_box(0);
    v___x_449_ = l_Lean_Meta_Sym_Arith_ofPoly___closed__12;
    v___x_450_ = l_Lean_Expr_const___override(v___x_449_, v___x_448_);
    return v___x_450_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = leanh::lean_box(0);
    v___x_456_ = l_Lean_Meta_Sym_Arith_ofPoly___closed__15;
    v___x_457_ = l_Lean_Expr_const___override(v___x_456_, v___x_455_);
    return v___x_457_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = leanh::lean_box(0);
    v___x_466_ = l_Lean_Meta_Sym_Arith_ofPoly___closed__18;
    v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_465_);
    return v___x_467_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ofPoly(
    mut v_p_468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_468_) == 0 {
                    v_k_469_ = leanh::lean_ctor_get(v_p_468_, 0);
                    leanh::lean_inc(v_k_469_);
                    leanh::lean_dec_ref_known(v_p_468_, 1);
                    v___x_470_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__3_once),
                        _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__3,
                    );
                    v___x_471_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4_once),
                        _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__4,
                    );
                    v___x_472_ = lean_int_dec_le(v___x_471_, v_k_469_);
                    if v___x_472_ == 0 {
                        v___x_473_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10_once),
                            _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__10,
                        );
                        v___x_474_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13_once),
                            _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__13,
                        );
                        v___x_475_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16_once),
                            _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__16,
                        );
                        v___x_476_ = lean_int_neg(v_k_469_);
                        leanh::lean_dec(v_k_469_);
                        v___x_477_ = l_Int_toNat(v___x_476_);
                        leanh::lean_dec(v___x_476_);
                        v___x_478_ = l_Lean_instToExprInt_mkNat(v___x_477_);
                        v___x_479_ = l_Lean_mkApp3(v___x_473_, v___x_474_, v___x_475_, v___x_478_);
                        v___x_480_ = l_Lean_Expr_app___override(v___x_470_, v___x_479_);
                        return v___x_480_;
                    } else {
                        v___x_481_ = l_Int_toNat(v_k_469_);
                        leanh::lean_dec(v_k_469_);
                        v___x_482_ = l_Lean_instToExprInt_mkNat(v___x_481_);
                        v___x_483_ = l_Lean_Expr_app___override(v___x_470_, v___x_482_);
                        return v___x_483_;
                    }
                } else {
                    v_k_484_ = leanh::lean_ctor_get(v_p_468_, 0);
                    leanh::lean_inc(v_k_484_);
                    v_v_485_ = leanh::lean_ctor_get(v_p_468_, 1);
                    leanh::lean_inc(v_v_485_);
                    v_p_486_ = leanh::lean_ctor_get(v_p_468_, 2);
                    leanh::lean_inc_ref(v_p_486_);
                    leanh::lean_dec_ref_known(v_p_468_, 3);
                    v___x_487_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__19),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__19_once),
                        _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__19,
                    );
                    v___x_493_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4_once),
                        _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__4,
                    );
                    v___x_494_ = lean_int_dec_le(v___x_493_, v_k_484_);
                    if v___x_494_ == 0 {
                        v___x_495_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10_once),
                            _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__10,
                        );
                        v___x_496_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13_once),
                            _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__13,
                        );
                        v___x_497_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16_once),
                            _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__16,
                        );
                        v___x_498_ = lean_int_neg(v_k_484_);
                        leanh::lean_dec(v_k_484_);
                        v___x_499_ = l_Int_toNat(v___x_498_);
                        leanh::lean_dec(v___x_498_);
                        v___x_500_ = l_Lean_instToExprInt_mkNat(v___x_499_);
                        v___x_501_ = l_Lean_mkApp3(v___x_495_, v___x_496_, v___x_497_, v___x_500_);
                        v___y_489_ = v___x_501_;
                        state = 1;
                        continue;
                    } else {
                        v___x_502_ = l_Int_toNat(v_k_484_);
                        leanh::lean_dec(v_k_484_);
                        v___x_503_ = l_Lean_instToExprInt_mkNat(v___x_502_);
                        v___y_489_ = v___x_503_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_490_ = l_Lean_Meta_Sym_Arith_ofMon(v_v_485_);
                v___x_491_ = l_Lean_Meta_Sym_Arith_ofPoly(v_p_486_);
                v___x_492_ = l_Lean_mkApp3(v___x_487_, v___y_489_, v___x_490_, v___x_491_);
                return v___x_492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_510_ = leanh::lean_box(0);
    v___x_511_ = l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1;
    v___x_512_ = l_Lean_mkConst(v___x_511_, v___x_510_);
    return v___x_512_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2,
    );
    v___x_514_ = l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0;
    v___x_515_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_515_, 0, v___x_514_);
    leanh::lean_ctor_set(v___x_515_, 1, v___x_513_);
    return v___x_515_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprPoly() -> *mut leanh::LeanObject {
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3,
    );
    return v___x_516_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = leanh::lean_box(0);
    v___x_525_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1;
    v___x_526_ = l_Lean_mkConst(v___x_525_, v___x_524_);
    return v___x_526_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_534_ = leanh::lean_box(0);
    v___x_535_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4;
    v___x_536_ = l_Lean_mkConst(v___x_535_, v___x_534_);
    return v___x_536_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = leanh::lean_box(0);
    v___x_545_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7;
    v___x_546_ = l_Lean_mkConst(v___x_545_, v___x_544_);
    return v___x_546_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11() -> *mut leanh::LeanObject
{
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = leanh::lean_box(0);
    v___x_555_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10;
    v___x_556_ = l_Lean_mkConst(v___x_555_, v___x_554_);
    return v___x_556_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13() -> *mut leanh::LeanObject
{
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = leanh::lean_box(0);
    v___x_564_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12;
    v___x_565_ = l_Lean_mkConst(v___x_564_, v___x_563_);
    return v___x_565_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15() -> *mut leanh::LeanObject
{
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = leanh::lean_box(0);
    v___x_573_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14;
    v___x_574_ = l_Lean_mkConst(v___x_573_, v___x_572_);
    return v___x_574_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18() -> *mut leanh::LeanObject
{
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = leanh::lean_box(0);
    v___x_583_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17;
    v___x_584_ = l_Lean_mkConst(v___x_583_, v___x_582_);
    return v___x_584_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21() -> *mut leanh::LeanObject
{
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = leanh::lean_box(0);
    v___x_593_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20;
    v___x_594_ = l_Lean_mkConst(v___x_593_, v___x_592_);
    return v___x_594_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24() -> *mut leanh::LeanObject
{
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = leanh::lean_box(0);
    v___x_603_ = l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23;
    v___x_604_ = l_Lean_mkConst(v___x_603_, v___x_602_);
    return v___x_604_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_ofRingExpr(
    mut v_e_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_605_) {
        0 => {
            let mut v_k_606_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_609_: u8 = 0;
            v_k_606_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc(v_k_606_);
            leanh::lean_dec_ref_known(v_e_605_, 1);
            v___x_607_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2,
            );
            v___x_608_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4_once),
                _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__4,
            );
            v___x_609_ = lean_int_dec_le(v___x_608_, v_k_606_);
            if v___x_609_ == 0 {
                let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_610_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10_once),
                    _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__10,
                );
                v___x_611_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13_once),
                    _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__13,
                );
                v___x_612_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16_once),
                    _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__16,
                );
                v___x_613_ = lean_int_neg(v_k_606_);
                leanh::lean_dec(v_k_606_);
                v___x_614_ = l_Int_toNat(v___x_613_);
                leanh::lean_dec(v___x_613_);
                v___x_615_ = l_Lean_instToExprInt_mkNat(v___x_614_);
                v___x_616_ = l_Lean_mkApp3(v___x_610_, v___x_611_, v___x_612_, v___x_615_);
                v___x_617_ = l_Lean_Expr_app___override(v___x_607_, v___x_616_);
                return v___x_617_;
            } else {
                let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_618_ = l_Int_toNat(v_k_606_);
                leanh::lean_dec(v_k_606_);
                v___x_619_ = l_Lean_instToExprInt_mkNat(v___x_618_);
                v___x_620_ = l_Lean_Expr_app___override(v___x_607_, v___x_619_);
                return v___x_620_;
            }
        }
        1 => {
            let mut v_k_621_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_k_621_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc(v_k_621_);
            leanh::lean_dec_ref_known(v_e_605_, 1);
            v___x_622_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5,
            );
            v___x_623_ = l_Lean_mkNatLit(v_k_621_);
            v___x_624_ = l_Lean_Expr_app___override(v___x_622_, v___x_623_);
            return v___x_624_;
        }
        2 => {
            let mut v_k_625_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_628_: u8 = 0;
            v_k_625_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc(v_k_625_);
            leanh::lean_dec_ref_known(v_e_605_, 1);
            v___x_626_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8,
            );
            v___x_627_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__4_once),
                _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__4,
            );
            v___x_628_ = lean_int_dec_le(v___x_627_, v_k_625_);
            if v___x_628_ == 0 {
                let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_629_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__10_once),
                    _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__10,
                );
                v___x_630_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__13_once),
                    _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__13,
                );
                v___x_631_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofPoly___closed__16_once),
                    _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__16,
                );
                v___x_632_ = lean_int_neg(v_k_625_);
                leanh::lean_dec(v_k_625_);
                v___x_633_ = l_Int_toNat(v___x_632_);
                leanh::lean_dec(v___x_632_);
                v___x_634_ = l_Lean_instToExprInt_mkNat(v___x_633_);
                v___x_635_ = l_Lean_mkApp3(v___x_629_, v___x_630_, v___x_631_, v___x_634_);
                v___x_636_ = l_Lean_Expr_app___override(v___x_626_, v___x_635_);
                return v___x_636_;
            } else {
                let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_637_ = l_Int_toNat(v_k_625_);
                leanh::lean_dec(v_k_625_);
                v___x_638_ = l_Lean_instToExprInt_mkNat(v___x_637_);
                v___x_639_ = l_Lean_Expr_app___override(v___x_626_, v___x_638_);
                return v___x_639_;
            }
        }
        3 => {
            let mut v_i_640_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_640_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc(v_i_640_);
            leanh::lean_dec_ref_known(v_e_605_, 1);
            v___x_641_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11,
            );
            v___x_642_ = l_Lean_mkNatLit(v_i_640_);
            v___x_643_ = l_Lean_Expr_app___override(v___x_641_, v___x_642_);
            return v___x_643_;
        }
        4 => {
            let mut v_a_644_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_644_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc_ref(v_a_644_);
            leanh::lean_dec_ref_known(v_e_605_, 1);
            v___x_645_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13,
            );
            v___x_646_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_644_);
            v___x_647_ = l_Lean_Expr_app___override(v___x_645_, v___x_646_);
            return v___x_647_;
        }
        5 => {
            let mut v_a_648_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_649_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_648_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc_ref(v_a_648_);
            v_b_649_ = leanh::lean_ctor_get(v_e_605_, 1);
            leanh::lean_inc_ref(v_b_649_);
            leanh::lean_dec_ref_known(v_e_605_, 2);
            v___x_650_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15,
            );
            v___x_651_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_648_);
            v___x_652_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_b_649_);
            v___x_653_ = l_Lean_mkAppB(v___x_650_, v___x_651_, v___x_652_);
            return v___x_653_;
        }
        6 => {
            let mut v_a_654_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_655_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_654_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc_ref(v_a_654_);
            v_b_655_ = leanh::lean_ctor_get(v_e_605_, 1);
            leanh::lean_inc_ref(v_b_655_);
            leanh::lean_dec_ref_known(v_e_605_, 2);
            v___x_656_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18,
            );
            v___x_657_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_654_);
            v___x_658_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_b_655_);
            v___x_659_ = l_Lean_mkAppB(v___x_656_, v___x_657_, v___x_658_);
            return v___x_659_;
        }
        7 => {
            let mut v_a_660_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_661_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_660_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc_ref(v_a_660_);
            v_b_661_ = leanh::lean_ctor_get(v_e_605_, 1);
            leanh::lean_inc_ref(v_b_661_);
            leanh::lean_dec_ref_known(v_e_605_, 2);
            v___x_662_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21,
            );
            v___x_663_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_660_);
            v___x_664_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_b_661_);
            v___x_665_ = l_Lean_mkAppB(v___x_662_, v___x_663_, v___x_664_);
            return v___x_665_;
        }
        _ => {
            let mut v_a_666_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_667_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_666_ = leanh::lean_ctor_get(v_e_605_, 0);
            leanh::lean_inc_ref(v_a_666_);
            v_k_667_ = leanh::lean_ctor_get(v_e_605_, 1);
            leanh::lean_inc(v_k_667_);
            leanh::lean_dec_ref_known(v_e_605_, 2);
            v___x_668_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24),
                core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_once),
                _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24,
            );
            v___x_669_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_666_);
            v___x_670_ = l_Lean_mkNatLit(v_k_667_);
            v___x_671_ = l_Lean_mkAppB(v___x_668_, v___x_669_, v___x_670_);
            return v___x_671_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = leanh::lean_box(0);
    v___x_679_ = l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1;
    v___x_680_ = l_Lean_mkConst(v___x_679_, v___x_678_);
    return v___x_680_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_681_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2,
    );
    v___x_682_ = l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0;
    v___x_683_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_683_, 0, v___x_682_);
    leanh::lean_ctor_set(v___x_683_, 1, v___x_681_);
    return v___x_683_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_instToExprExpr() -> *mut leanh::LeanObject {
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3_once),
        _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3,
    );
    return v___x_684_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_ToExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_Arith_instToExprPower = _init_l_Lean_Meta_Sym_Arith_instToExprPower();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprPower);
    l_Lean_Meta_Sym_Arith_instToExprMon = _init_l_Lean_Meta_Sym_Arith_instToExprMon();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprMon);
    l_Lean_Meta_Sym_Arith_instToExprPoly = _init_l_Lean_Meta_Sym_Arith_instToExprPoly();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprPoly);
    l_Lean_Meta_Sym_Arith_instToExprExpr = _init_l_Lean_Meta_Sym_Arith_instToExprExpr();
    leanh::lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprExpr);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_ToExpr(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_ToExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_ToExpr(builtin);
}