// Lean compiler output
// Module: Lean.Meta.HasNotBit
// Imports: Lean.Meta.Basic Lean.Meta.MatchUtil
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_nat_lor, lean_nat_shiftl,
    lean_panic_fn_borrowed, lean_usize_add, lean_usize_dec_lt, lean_whnf,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hasFVar,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkRawNatLit, l_Lean_reflBoolTrue,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::MatchUtil::{
    initialize_Lean_Meta_MatchUtil, l_Lean_Meta_matchNe_x3f, runtime_initialize_Lean_Meta_MatchUtil,
};
pub static l_mkHasNotBit___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_mkHasNotBit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut leanh::LeanObject;
pub static l_mkHasNotBit___closed__1_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [104, 97, 115, 78, 111, 116, 66, 105, 116, 0],
    };
static mut l_mkHasNotBit___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBit___closed__1_value) as *mut leanh::LeanObject;
static l_mkHasNotBit___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
pub static l_mkHasNotBit___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBit___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_mkHasNotBit___closed__1_value) as *mut leanh::LeanObject,
            6351501397486105973 as *mut leanh::LeanObject,
        ],
    };
static mut l_mkHasNotBit___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBit___closed__2_value) as *mut leanh::LeanObject;
static mut l_mkHasNotBit___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBit___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00mkHasNotBitProof_spec__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_mkHasNotBitProof___closed__0_value: leanh::LeanStringObject<19> =
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
            110, 101, 95, 111, 102, 95, 98, 101, 113, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
        ],
    };
static mut l_mkHasNotBitProof___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__0_value) as *mut leanh::LeanObject;
static l_mkHasNotBitProof___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
pub static l_mkHasNotBitProof___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__0_value)
                as *mut leanh::LeanObject,
            1750192217580950936 as *mut leanh::LeanObject,
        ],
    };
static mut l_mkHasNotBitProof___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__1_value) as *mut leanh::LeanObject;
static mut l_mkHasNotBitProof___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__3_value: leanh::LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_mkHasNotBitProof___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__3_value) as *mut leanh::LeanObject;
pub static l_mkHasNotBitProof___closed__4_value: leanh::LeanStringObject<5> =
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
        m_data: [114, 101, 102, 108, 0],
    };
static mut l_mkHasNotBitProof___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__4_value) as *mut leanh::LeanObject;
static l_mkHasNotBitProof___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__3_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
pub static l_mkHasNotBitProof___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__4_value)
                as *mut leanh::LeanObject,
            13480818501600609864 as *mut leanh::LeanObject,
        ],
    };
static mut l_mkHasNotBitProof___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__5_value) as *mut leanh::LeanObject;
static mut l_mkHasNotBitProof___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_mkHasNotBitProof___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_mkHasNotBitProof___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__9_value: leanh::LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_mkHasNotBitProof___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__9_value) as *mut leanh::LeanObject;
pub static l_mkHasNotBitProof___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__9_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
static mut l_mkHasNotBitProof___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__10_value) as *mut leanh::LeanObject;
static mut l_mkHasNotBitProof___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__12_value: leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_mkHasNotBitProof___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__12_value) as *mut leanh::LeanObject;
static l_mkHasNotBitProof___closed__13_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__9_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_mkHasNotBitProof___closed__13_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__13_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_mkHasNotBitProof___closed__12_value)
                as *mut leanh::LeanObject,
            15761733860085307253 as *mut leanh::LeanObject,
        ],
    };
static mut l_mkHasNotBitProof___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__13_value) as *mut leanh::LeanObject;
static mut l_mkHasNotBitProof___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_mkHasNotBitProof___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__16_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 72, 97, 115, 78, 111, 116, 66, 105, 116, 0,
        ],
    };
static mut l_mkHasNotBitProof___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__16_value) as *mut leanh::LeanObject;
pub static l_mkHasNotBitProof___closed__17_value: leanh::LeanStringObject<17> =
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
            109, 107, 72, 97, 115, 78, 111, 116, 66, 105, 116, 80, 114, 111, 111, 102, 0,
        ],
    };
static mut l_mkHasNotBitProof___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__17_value) as *mut leanh::LeanObject;
pub static l_mkHasNotBitProof___closed__18_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_mkHasNotBitProof___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__18_value) as *mut leanh::LeanObject;
static mut l_mkHasNotBitProof___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkHasNotBitProof___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_refutableHasNotBit_x3f___closed__0_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            101, 113, 95, 111, 102, 95, 98, 101, 113, 95, 101, 113, 95, 116, 114, 117, 101, 0,
        ],
    };
static mut l_refutableHasNotBit_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static l_refutableHasNotBit_x3f___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
pub static l_refutableHasNotBit_x3f___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            13284083376251288999 as *mut leanh::LeanObject,
        ],
    };
static mut l_refutableHasNotBit_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_refutableHasNotBit_x3f___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_refutableHasNotBit_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_refutableHasNotBit_x3f___closed__3_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            114, 101, 102, 117, 116, 97, 98, 108, 101, 72, 97, 115, 78, 111, 116, 66, 105, 116, 63,
            0,
        ],
    };
static mut l_refutableHasNotBit_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_refutableHasNotBit_x3f___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_refutableHasNotBit_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(
    mut v_as_298_: *mut leanh::LeanObject,
    mut v_sz_299_: usize,
    mut v_i_300_: usize,
    mut v_b_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_302_: u8 = 0;
    let mut v_a_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: usize = 0;
    let mut v___x_308_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_302_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
                if v___x_302_ == 0 {
                    return v_b_301_;
                } else {
                    v_a_303_ = lean_array_uget_borrowed(v_as_298_, v_i_300_);
                    v___x_304_ = leanh::lean_unsigned_to_nat(1);
                    v___x_305_ = lean_nat_shiftl(v___x_304_, v_a_303_);
                    v___x_306_ = lean_nat_lor(v_b_301_, v___x_305_);
                    leanh::lean_dec(v___x_305_);
                    leanh::lean_dec(v_b_301_);
                    v___x_307_ = 1usize;
                    v___x_308_ = lean_usize_add(v_i_300_, v___x_307_);
                    v_i_300_ = v___x_308_;
                    v_b_301_ = v___x_306_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0___boxed(
    mut v_as_310_: *mut leanh::LeanObject,
    mut v_sz_311_: *mut leanh::LeanObject,
    mut v_i_312_: *mut leanh::LeanObject,
    mut v_b_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_314_: usize = 0;
    let mut v_i_boxed_315_: usize = 0;
    let mut v_res_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_314_ = leanh::lean_unbox_usize(v_sz_311_);
    leanh::lean_dec(v_sz_311_);
    v_i_boxed_315_ = leanh::lean_unbox_usize(v_i_312_);
    leanh::lean_dec(v_i_312_);
    v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(v_as_310_, v_sz_boxed_314_, v_i_boxed_315_, v_b_313_);
    leanh::lean_dec_ref(v_as_310_);
    return v_res_316_;
}
pub unsafe fn _init_l_mkHasNotBit___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = leanh::lean_box(0);
    v___x_323_ = l_mkHasNotBit___closed__2;
    v___x_324_ = l_Lean_mkConst(v___x_323_, v___x_322_);
    return v___x_324_;
}
pub unsafe fn l_mkHasNotBit(
    mut v_e_325_: *mut leanh::LeanObject,
    mut v_ns_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mask_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_328_: usize = 0;
    let mut v___x_329_: usize = 0;
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mask_327_ = leanh::lean_unsigned_to_nat(0);
    v_sz_328_ = lean_array_size(v_ns_326_);
    v___x_329_ = 0usize;
    v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(v_ns_326_, v_sz_328_, v___x_329_, v_mask_327_);
    v___x_331_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3),
        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3_once),
        _init_l_mkHasNotBit___closed__3,
    );
    v___x_332_ = l_Lean_mkRawNatLit(v___x_330_);
    v___x_333_ = l_Lean_mkAppB(v___x_331_, v___x_332_, v_e_325_);
    return v___x_333_;
}
pub unsafe fn l_mkHasNotBit___boxed(
    mut v_e_334_: *mut leanh::LeanObject,
    mut v_ns_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_336_ = l_mkHasNotBit(v_e_334_, v_ns_335_);
    leanh::lean_dec_ref(v_ns_335_);
    return v_res_336_;
}
pub unsafe fn l_panic___at___00mkHasNotBitProof_spec__0(
    mut v_msg_338_: *mut leanh::LeanObject,
    mut v___y_339_: *mut leanh::LeanObject,
    mut v___y_340_: *mut leanh::LeanObject,
    mut v___y_341_: *mut leanh::LeanObject,
    mut v___y_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344__overap_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_344_ = l_panic___at___00mkHasNotBitProof_spec__0___closed__0;
    v___x_344__overap_345_ = lean_panic_fn_borrowed(v___f_344_, v_msg_338_);
    leanh::lean_inc(v___y_342_);
    leanh::lean_inc_ref(v___y_341_);
    leanh::lean_inc(v___y_340_);
    leanh::lean_inc_ref(v___y_339_);
    v___x_346_ = leanh::lean_apply_5(
        v___x_344__overap_345_,
        v___y_339_,
        v___y_340_,
        v___y_341_,
        v___y_342_,
        leanh::lean_box(0),
    );
    return v___x_346_;
}
pub unsafe fn l_panic___at___00mkHasNotBitProof_spec__0___boxed(
    mut v_msg_347_: *mut leanh::LeanObject,
    mut v___y_348_: *mut leanh::LeanObject,
    mut v___y_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
    mut v___y_351_: *mut leanh::LeanObject,
    mut v___y_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_panic___at___00mkHasNotBitProof_spec__0(
        v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_,
    );
    leanh::lean_dec(v___y_351_);
    leanh::lean_dec_ref(v___y_350_);
    leanh::lean_dec(v___y_349_);
    leanh::lean_dec_ref(v___y_348_);
    return v_res_353_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = leanh::lean_box(0);
    v___x_359_ = l_mkHasNotBitProof___closed__1;
    v___x_360_ = l_Lean_mkConst(v___x_359_, v___x_358_);
    return v___x_360_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = leanh::lean_unsigned_to_nat(1);
    v___x_367_ = l_Lean_Level_ofNat(v___x_366_);
    return v___x_367_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = leanh::lean_box(0);
    v___x_369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__6),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__6_once),
        _init_l_mkHasNotBitProof___closed__6,
    );
    v___x_370_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_370_, 0, v___x_369_);
    leanh::lean_ctor_set(v___x_370_, 1, v___x_368_);
    return v___x_370_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__7),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__7_once),
        _init_l_mkHasNotBitProof___closed__7,
    );
    v___x_372_ = l_mkHasNotBitProof___closed__5;
    v___x_373_ = l_Lean_mkConst(v___x_372_, v___x_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = leanh::lean_box(0);
    v___x_378_ = l_mkHasNotBitProof___closed__10;
    v___x_379_ = l_Lean_mkConst(v___x_378_, v___x_377_);
    return v___x_379_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ = leanh::lean_box(0);
    v___x_385_ = l_mkHasNotBitProof___closed__13;
    v___x_386_ = l_Lean_mkConst(v___x_385_, v___x_384_);
    return v___x_386_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__14),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__14_once),
        _init_l_mkHasNotBitProof___closed__14,
    );
    v___x_388_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__11),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__11_once),
        _init_l_mkHasNotBitProof___closed__11,
    );
    v___x_389_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__8),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__8_once),
        _init_l_mkHasNotBitProof___closed__8,
    );
    v___x_390_ = l_Lean_mkAppB(v___x_389_, v___x_388_, v___x_387_);
    return v___x_390_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = l_mkHasNotBitProof___closed__18;
    v___x_395_ = leanh::lean_unsigned_to_nat(57);
    v___x_396_ = leanh::lean_unsigned_to_nat(33);
    v___x_397_ = l_mkHasNotBitProof___closed__17;
    v___x_398_ = l_mkHasNotBitProof___closed__16;
    v___x_399_ =
        l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
    return v___x_399_;
}
pub unsafe fn l_mkHasNotBitProof(
    mut v_e_400_: *mut leanh::LeanObject,
    mut v_ns_401_: *mut leanh::LeanObject,
    mut v_a_402_: *mut leanh::LeanObject,
    mut v_a_403_: *mut leanh::LeanObject,
    mut v_a_404_: *mut leanh::LeanObject,
    mut v_a_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v_val_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_425_: u8 = 0;
    let mut v_a_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_407_ = l_mkHasNotBit(v_e_400_, v_ns_401_);
                v___x_408_ =
                    l_Lean_Meta_matchNe_x3f(v___x_407_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
                if leanh::lean_obj_tag(v___x_408_) == 0 {
                    v_a_409_ = leanh::lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_425_ = (!leanh::lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_425_ == 0 {
                        v___x_411_ = v___x_408_;
                        v_isShared_412_ = v_isSharedCheck_425_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_409_);
                        leanh::lean_dec(v___x_408_);
                        v___x_411_ = leanh::lean_box(0);
                        v_isShared_412_ = v_isSharedCheck_425_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_426_ = leanh::lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_433_ = (!leanh::lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_433_ == 0 {
                        v___x_428_ = v___x_408_;
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_426_);
                        leanh::lean_dec(v___x_408_);
                        v___x_428_ = leanh::lean_box(0);
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_409_) == 1 {
                    v_val_413_ = leanh::lean_ctor_get(v_a_409_, 0);
                    leanh::lean_inc(v_val_413_);
                    leanh::lean_dec_ref_known(v_a_409_, 1);
                    v_snd_414_ = leanh::lean_ctor_get(v_val_413_, 1);
                    leanh::lean_inc(v_snd_414_);
                    leanh::lean_dec(v_val_413_);
                    v_fst_415_ = leanh::lean_ctor_get(v_snd_414_, 0);
                    leanh::lean_inc(v_fst_415_);
                    v_snd_416_ = leanh::lean_ctor_get(v_snd_414_, 1);
                    leanh::lean_inc(v_snd_416_);
                    leanh::lean_dec(v_snd_414_);
                    v___x_417_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__2),
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__2_once),
                        _init_l_mkHasNotBitProof___closed__2,
                    );
                    v___x_418_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__15),
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__15_once),
                        _init_l_mkHasNotBitProof___closed__15,
                    );
                    v___x_419_ = l_Lean_mkApp3(v___x_417_, v_fst_415_, v_snd_416_, v___x_418_);
                    if v_isShared_412_ == 0 {
                        leanh::lean_ctor_set(v___x_411_, 0, v___x_419_);
                        v___x_421_ = v___x_411_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
                        v___x_421_ = v_reuseFailAlloc_422_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_411_);
                    leanh::lean_dec(v_a_409_);
                    v___x_423_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__19),
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__19_once),
                        _init_l_mkHasNotBitProof___closed__19,
                    );
                    v___x_424_ = l_panic___at___00mkHasNotBitProof_spec__0(
                        v___x_423_, v_a_402_, v_a_403_, v_a_404_, v_a_405_,
                    );
                    return v___x_424_;
                }
            }
            2 => {
                return v___x_421_;
            }
            3 => {
                if v_isShared_429_ == 0 {
                    v___x_431_ = v___x_428_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
                    v___x_431_ = v_reuseFailAlloc_432_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkHasNotBitProof___boxed(
    mut v_e_434_: *mut leanh::LeanObject,
    mut v_ns_435_: *mut leanh::LeanObject,
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_a_437_: *mut leanh::LeanObject,
    mut v_a_438_: *mut leanh::LeanObject,
    mut v_a_439_: *mut leanh::LeanObject,
    mut v_a_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_441_ = l_mkHasNotBitProof(v_e_434_, v_ns_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
    leanh::lean_dec(v_a_439_);
    leanh::lean_dec_ref(v_a_438_);
    leanh::lean_dec(v_a_437_);
    leanh::lean_dec_ref(v_a_436_);
    leanh::lean_dec_ref(v_ns_435_);
    return v_res_441_;
}
pub unsafe fn l_isHasNotBit_x3f(
    mut v_e_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    v___x_443_ = l_Lean_Expr_cleanupAnnotations(v_e_442_);
    v___x_444_ = l_Lean_Expr_isApp(v___x_443_);
    if v___x_444_ == 0 {
        let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_443_);
        v___x_445_ = leanh::lean_box(0);
        return v___x_445_;
    } else {
        let mut v_arg_446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: u8 = 0;
        v_arg_446_ = leanh::lean_ctor_get(v___x_443_, 1);
        leanh::lean_inc_ref(v_arg_446_);
        v___x_447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_443_);
        v___x_448_ = l_Lean_Expr_isApp(v___x_447_);
        if v___x_448_ == 0 {
            let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_447_);
            leanh::lean_dec_ref(v_arg_446_);
            v___x_449_ = leanh::lean_box(0);
            return v___x_449_;
        } else {
            let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_452_: u8 = 0;
            v___x_450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_447_);
            v___x_451_ = l_mkHasNotBit___closed__2;
            v___x_452_ = l_Lean_Expr_isConstOf(v___x_450_, v___x_451_);
            leanh::lean_dec_ref(v___x_450_);
            if v___x_452_ == 0 {
                let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_arg_446_);
                v___x_453_ = leanh::lean_box(0);
                return v___x_453_;
            } else {
                let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_454_, 0, v_arg_446_);
                return v___x_454_;
            }
        }
    }
}
pub unsafe fn l_panic___at___00refutableHasNotBit_x3f_spec__0(
    mut v_msg_455_: *mut leanh::LeanObject,
    mut v___y_456_: *mut leanh::LeanObject,
    mut v___y_457_: *mut leanh::LeanObject,
    mut v___y_458_: *mut leanh::LeanObject,
    mut v___y_459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859__overap_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_461_ = l_panic___at___00mkHasNotBitProof_spec__0___closed__0;
    v___x_1859__overap_462_ = lean_panic_fn_borrowed(v___f_461_, v_msg_455_);
    leanh::lean_inc(v___y_459_);
    leanh::lean_inc_ref(v___y_458_);
    leanh::lean_inc(v___y_457_);
    leanh::lean_inc_ref(v___y_456_);
    v___x_463_ = leanh::lean_apply_5(
        v___x_1859__overap_462_,
        v___y_456_,
        v___y_457_,
        v___y_458_,
        v___y_459_,
        leanh::lean_box(0),
    );
    return v___x_463_;
}
pub unsafe fn l_panic___at___00refutableHasNotBit_x3f_spec__0___boxed(
    mut v_msg_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
    mut v___y_467_: *mut leanh::LeanObject,
    mut v___y_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_panic___at___00refutableHasNotBit_x3f_spec__0(
        v_msg_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_,
    );
    leanh::lean_dec(v___y_468_);
    leanh::lean_dec_ref(v___y_467_);
    leanh::lean_dec(v___y_466_);
    leanh::lean_dec_ref(v___y_465_);
    return v_res_470_;
}
pub unsafe fn _init_l_refutableHasNotBit_x3f___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = leanh::lean_box(0);
    v___x_476_ = l_refutableHasNotBit_x3f___closed__1;
    v___x_477_ = l_Lean_mkConst(v___x_476_, v___x_475_);
    return v___x_477_;
}
pub unsafe fn _init_l_refutableHasNotBit_x3f___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_479_ = l_mkHasNotBitProof___closed__18;
    v___x_480_ = leanh::lean_unsigned_to_nat(84);
    v___x_481_ = leanh::lean_unsigned_to_nat(53);
    v___x_482_ = l_refutableHasNotBit_x3f___closed__3;
    v___x_483_ = l_mkHasNotBitProof___closed__16;
    v___x_484_ =
        l_mkPanicMessageWithDecl(v___x_483_, v___x_482_, v___x_481_, v___x_480_, v___x_479_);
    return v___x_484_;
}
pub unsafe fn l_refutableHasNotBit_x3f(
    mut v_e_485_: *mut leanh::LeanObject,
    mut v_a_486_: *mut leanh::LeanObject,
    mut v_a_487_: *mut leanh::LeanObject,
    mut v_a_488_: *mut leanh::LeanObject,
    mut v_a_489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_495_: u8 = 0;
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    let mut v_arg_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u8 = 0;
    let mut v_arg_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_514_: u8 = 0;
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_523_: u8 = 0;
    let mut v_snd_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_531_: u8 = 0;
    let mut v___x_532_: u8 = 0;
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_546_: u8 = 0;
    let mut v_a_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_550_: u8 = 0;
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut v_isSharedCheck_555_: u8 = 0;
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_561_: u8 = 0;
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_a_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_578_: u8 = 0;
    let mut v_isSharedCheck_579_: u8 = 0;
    let mut v_a_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_583_: u8 = 0;
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_491_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_485_, v_a_487_);
                if leanh::lean_obj_tag(v___x_491_) == 0 {
                    v_a_492_ = leanh::lean_ctor_get(v___x_491_, 0);
                    v_isSharedCheck_579_ = (!leanh::lean_is_exclusive(v___x_491_)) as u8;
                    if v_isSharedCheck_579_ == 0 {
                        v___x_494_ = v___x_491_;
                        v_isShared_495_ = v_isSharedCheck_579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_492_);
                        leanh::lean_dec(v___x_491_);
                        v___x_494_ = leanh::lean_box(0);
                        v_isShared_495_ = v_isSharedCheck_579_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_580_ = leanh::lean_ctor_get(v___x_491_, 0);
                    v_isSharedCheck_587_ = (!leanh::lean_is_exclusive(v___x_491_)) as u8;
                    if v_isSharedCheck_587_ == 0 {
                        v___x_582_ = v___x_491_;
                        v_isShared_583_ = v_isSharedCheck_587_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_580_);
                        leanh::lean_dec(v___x_491_);
                        v___x_582_ = leanh::lean_box(0);
                        v_isShared_583_ = v_isSharedCheck_587_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_501_ = l_Lean_Expr_cleanupAnnotations(v_a_492_);
                v___x_502_ = l_Lean_Expr_isApp(v___x_501_);
                if v___x_502_ == 0 {
                    leanh::lean_dec_ref(v___x_501_);
                    state = 2;
                    continue;
                } else {
                    v_arg_503_ = leanh::lean_ctor_get(v___x_501_, 1);
                    leanh::lean_inc_ref(v_arg_503_);
                    v___x_504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_501_);
                    v___x_505_ = l_Lean_Expr_isApp(v___x_504_);
                    if v___x_505_ == 0 {
                        leanh::lean_dec_ref(v___x_504_);
                        leanh::lean_dec_ref(v_arg_503_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_506_ = leanh::lean_ctor_get(v___x_504_, 1);
                        leanh::lean_inc_ref(v_arg_506_);
                        v___x_507_ = l_Lean_Expr_appFnCleanup___redArg(v___x_504_);
                        v___x_508_ = l_mkHasNotBit___closed__2;
                        v___x_509_ = l_Lean_Expr_isConstOf(v___x_507_, v___x_508_);
                        leanh::lean_dec_ref(v___x_507_);
                        if v___x_509_ == 0 {
                            leanh::lean_dec_ref(v_arg_506_);
                            leanh::lean_dec_ref(v_arg_503_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_494_);
                            leanh::lean_inc(v_a_489_);
                            leanh::lean_inc_ref(v_a_488_);
                            leanh::lean_inc(v_a_487_);
                            leanh::lean_inc_ref(v_a_486_);
                            v___x_510_ =
                                lean_whnf(v_arg_503_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
                            if leanh::lean_obj_tag(v___x_510_) == 0 {
                                v_a_511_ = leanh::lean_ctor_get(v___x_510_, 0);
                                v_isSharedCheck_570_ =
                                    (!leanh::lean_is_exclusive(v___x_510_)) as u8;
                                if v_isSharedCheck_570_ == 0 {
                                    v___x_513_ = v___x_510_;
                                    v_isShared_514_ = v_isSharedCheck_570_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_511_);
                                    leanh::lean_dec(v___x_510_);
                                    v___x_513_ = leanh::lean_box(0);
                                    v_isShared_514_ = v_isSharedCheck_570_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_arg_506_);
                                v_a_571_ = leanh::lean_ctor_get(v___x_510_, 0);
                                v_isSharedCheck_578_ =
                                    (!leanh::lean_is_exclusive(v___x_510_)) as u8;
                                if v_isSharedCheck_578_ == 0 {
                                    v___x_573_ = v___x_510_;
                                    v_isShared_574_ = v_isSharedCheck_578_;
                                    state = 15;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_571_);
                                    leanh::lean_dec(v___x_510_);
                                    v___x_573_ = leanh::lean_box(0);
                                    v_isShared_574_ = v_isSharedCheck_578_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_497_ = leanh::lean_box(0);
                if v_isShared_495_ == 0 {
                    leanh::lean_ctor_set(v___x_494_, 0, v___x_497_);
                    v___x_499_ = v___x_494_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_500_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
                    v___x_499_ = v_reuseFailAlloc_500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_499_;
            }
            4 => {
                v___x_515_ = l_Lean_Expr_hasFVar(v_a_511_);
                if v___x_515_ == 0 {
                    leanh::lean_del_object(v___x_513_);
                    v___x_516_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3),
                        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3_once),
                        _init_l_mkHasNotBit___closed__3,
                    );
                    v___x_517_ = l_Lean_mkAppB(v___x_516_, v_arg_506_, v_a_511_);
                    v___x_518_ =
                        l_Lean_Meta_matchNe_x3f(v___x_517_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
                    if leanh::lean_obj_tag(v___x_518_) == 0 {
                        v_a_519_ = leanh::lean_ctor_get(v___x_518_, 0);
                        leanh::lean_inc(v_a_519_);
                        leanh::lean_dec_ref_known(v___x_518_, 1);
                        if leanh::lean_obj_tag(v_a_519_) == 1 {
                            v_val_520_ = leanh::lean_ctor_get(v_a_519_, 0);
                            v_isSharedCheck_555_ =
                                (!leanh::lean_is_exclusive(v_a_519_)) as u8;
                            if v_isSharedCheck_555_ == 0 {
                                v___x_522_ = v_a_519_;
                                v_isShared_523_ = v_isSharedCheck_555_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_520_);
                                leanh::lean_dec(v_a_519_);
                                v___x_522_ = leanh::lean_box(0);
                                v_isShared_523_ = v_isSharedCheck_555_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_519_);
                            v___x_556_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__4),
                                core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__4_once),
                                _init_l_refutableHasNotBit_x3f___closed__4,
                            );
                            v___x_557_ = l_panic___at___00refutableHasNotBit_x3f_spec__0(
                                v___x_556_, v_a_486_, v_a_487_, v_a_488_, v_a_489_,
                            );
                            return v___x_557_;
                        }
                    } else {
                        v_a_558_ = leanh::lean_ctor_get(v___x_518_, 0);
                        v_isSharedCheck_565_ = (!leanh::lean_is_exclusive(v___x_518_)) as u8;
                        if v_isSharedCheck_565_ == 0 {
                            v___x_560_ = v___x_518_;
                            v_isShared_561_ = v_isSharedCheck_565_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_558_);
                            leanh::lean_dec(v___x_518_);
                            v___x_560_ = leanh::lean_box(0);
                            v_isShared_561_ = v_isSharedCheck_565_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_511_);
                    leanh::lean_dec_ref(v_arg_506_);
                    v___x_566_ = leanh::lean_box(0);
                    if v_isShared_514_ == 0 {
                        leanh::lean_ctor_set(v___x_513_, 0, v___x_566_);
                        v___x_568_ = v___x_513_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
                        v___x_568_ = v_reuseFailAlloc_569_;
                        state = 14;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_524_ = leanh::lean_ctor_get(v_val_520_, 1);
                leanh::lean_inc(v_snd_524_);
                leanh::lean_dec(v_val_520_);
                v_fst_525_ = leanh::lean_ctor_get(v_snd_524_, 0);
                leanh::lean_inc_n(v_fst_525_, 2);
                v_snd_526_ = leanh::lean_ctor_get(v_snd_524_, 1);
                leanh::lean_inc_n(v_snd_526_, 2);
                leanh::lean_dec(v_snd_524_);
                v___x_527_ = l_Lean_Meta_isExprDefEq(
                    v_fst_525_, v_snd_526_, v_a_486_, v_a_487_, v_a_488_, v_a_489_,
                );
                if leanh::lean_obj_tag(v___x_527_) == 0 {
                    v_a_528_ = leanh::lean_ctor_get(v___x_527_, 0);
                    v_isSharedCheck_546_ = (!leanh::lean_is_exclusive(v___x_527_)) as u8;
                    if v_isSharedCheck_546_ == 0 {
                        v___x_530_ = v___x_527_;
                        v_isShared_531_ = v_isSharedCheck_546_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_528_);
                        leanh::lean_dec(v___x_527_);
                        v___x_530_ = leanh::lean_box(0);
                        v_isShared_531_ = v_isSharedCheck_546_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_526_);
                    leanh::lean_dec(v_fst_525_);
                    leanh::lean_del_object(v___x_522_);
                    v_a_547_ = leanh::lean_ctor_get(v___x_527_, 0);
                    v_isSharedCheck_554_ = (!leanh::lean_is_exclusive(v___x_527_)) as u8;
                    if v_isSharedCheck_554_ == 0 {
                        v___x_549_ = v___x_527_;
                        v_isShared_550_ = v_isSharedCheck_554_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_547_);
                        leanh::lean_dec(v___x_527_);
                        v___x_549_ = leanh::lean_box(0);
                        v_isShared_550_ = v_isSharedCheck_554_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_532_ = (leanh::lean_unbox(v_a_528_) as u8);
                leanh::lean_dec(v_a_528_);
                if v___x_532_ == 0 {
                    leanh::lean_dec(v_snd_526_);
                    leanh::lean_dec(v_fst_525_);
                    leanh::lean_del_object(v___x_522_);
                    v___x_533_ = leanh::lean_box(0);
                    if v_isShared_531_ == 0 {
                        leanh::lean_ctor_set(v___x_530_, 0, v___x_533_);
                        v___x_535_ = v___x_530_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
                        v___x_535_ = v_reuseFailAlloc_536_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_537_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__2),
                        core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__2_once),
                        _init_l_refutableHasNotBit_x3f___closed__2,
                    );
                    v___x_538_ = l_Lean_reflBoolTrue;
                    v___x_539_ = l_Lean_mkApp3(v___x_537_, v_fst_525_, v_snd_526_, v___x_538_);
                    if v_isShared_523_ == 0 {
                        leanh::lean_ctor_set(v___x_522_, 0, v___x_539_);
                        v___x_541_ = v___x_522_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_539_);
                        v___x_541_ = v_reuseFailAlloc_545_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_535_;
            }
            8 => {
                if v_isShared_531_ == 0 {
                    leanh::lean_ctor_set(v___x_530_, 0, v___x_541_);
                    v___x_543_ = v___x_530_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
                    v___x_543_ = v_reuseFailAlloc_544_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_543_;
            }
            10 => {
                if v_isShared_550_ == 0 {
                    v___x_552_ = v___x_549_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
                    v___x_552_ = v_reuseFailAlloc_553_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_552_;
            }
            12 => {
                if v_isShared_561_ == 0 {
                    v___x_563_ = v___x_560_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_564_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
                    v___x_563_ = v_reuseFailAlloc_564_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_563_;
            }
            14 => {
                return v___x_568_;
            }
            15 => {
                if v_isShared_574_ == 0 {
                    v___x_576_ = v___x_573_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_576_;
            }
            17 => {
                if v_isShared_583_ == 0 {
                    v___x_585_ = v___x_582_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
                    v___x_585_ = v_reuseFailAlloc_586_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_refutableHasNotBit_x3f___boxed(
    mut v_e_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
    mut v_a_590_: *mut leanh::LeanObject,
    mut v_a_591_: *mut leanh::LeanObject,
    mut v_a_592_: *mut leanh::LeanObject,
    mut v_a_593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_594_ = l_refutableHasNotBit_x3f(v_e_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
    leanh::lean_dec(v_a_592_);
    leanh::lean_dec_ref(v_a_591_);
    leanh::lean_dec(v_a_590_);
    leanh::lean_dec_ref(v_a_589_);
    return v_res_594_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_HasNotBit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_HasNotBit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_HasNotBit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_MatchUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_HasNotBit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_HasNotBit(builtin);
}