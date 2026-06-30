// Lean compiler output
// Module: Lean.HeadIndex
// Imports: Lean.Expr
use crate::ffi::{
    lean_expr_instantiate1, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_to_int, lean_panic_fn_borrowed, lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Literal_hash, l_Lean_instBEqFVarId_beq, l_Lean_instBEqLiteral_beq,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableFVarId_hash, l_Lean_instHashableMVarId_hash,
    l_Lean_instReprLiteral_repr, runtime_initialize_Lean_Expr,
};
pub static l_Lean_instInhabitedHeadIndex_default___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_instInhabitedHeadIndex_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedHeadIndex_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedHeadIndex_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedHeadIndex_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedHeadIndex: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedHeadIndex_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instBEqHeadIndex___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqHeadIndex_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqHeadIndex___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqHeadIndex___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqHeadIndex: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqHeadIndex___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__0_value: leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 115, 111, 114, 116,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__2_value: leanh::LeanStringObject<19> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 108, 97, 109, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__4_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 102, 111, 114, 97,
            108, 108, 69, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__6_value: leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 102, 118, 97, 114,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__7_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprHeadIndex_repr___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprHeadIndex_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprHeadIndex_repr___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprHeadIndex_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprHeadIndex_repr___closed__11_value: leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 109, 118, 97, 114,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__12_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__12_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__14_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 99, 111, 110, 115,
            116, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__15_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__16_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__15_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__17_value: leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 112, 114, 111, 106,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__18_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__19_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__18_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__20_value: leanh::LeanStringObject<19> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 108, 105, 116, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__22_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__21_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprHeadIndex___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprHeadIndex_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprHeadIndex___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprHeadIndex: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_HeadIndex_hash___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_HeadIndex_hash___closed__0: u64 = 0;
static mut l_Lean_HeadIndex_hash___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_HeadIndex_hash___closed__1: u64 = 0;
pub static l_Lean_instHashableHeadIndex___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_HeadIndex_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableHeadIndex___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableHeadIndex___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instHashableHeadIndex: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableHeadIndex___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((5 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((6 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((7 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value:
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
        76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 0,
    ],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value:
    leanh::LeanStringObject<52> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110,
        100, 101, 120, 46, 48, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 116, 111, 72, 101,
        97, 100, 73, 110, 100, 101, 120, 83, 108, 111, 119, 0,
    ],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115,
        105, 111, 110, 32, 107, 105, 110, 100, 0,
    ],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_HeadIndex_ctorIdx(
    mut v_x_447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_447_) {
        0 => {
            let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_448_ = leanh::lean_unsigned_to_nat(0);
            return v___x_448_;
        }
        1 => {
            let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_449_ = leanh::lean_unsigned_to_nat(1);
            return v___x_449_;
        }
        2 => {
            let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_450_ = leanh::lean_unsigned_to_nat(2);
            return v___x_450_;
        }
        3 => {
            let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_451_ = leanh::lean_unsigned_to_nat(3);
            return v___x_451_;
        }
        4 => {
            let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_452_ = leanh::lean_unsigned_to_nat(4);
            return v___x_452_;
        }
        5 => {
            let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_453_ = leanh::lean_unsigned_to_nat(5);
            return v___x_453_;
        }
        6 => {
            let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_454_ = leanh::lean_unsigned_to_nat(6);
            return v___x_454_;
        }
        _ => {
            let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_455_ = leanh::lean_unsigned_to_nat(7);
            return v___x_455_;
        }
    }
}
pub unsafe fn l_Lean_HeadIndex_ctorIdx___boxed(
    mut v_x_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Lean_HeadIndex_ctorIdx(v_x_456_);
    leanh::lean_dec(v_x_456_);
    return v_res_457_;
}
pub unsafe fn l_Lean_HeadIndex_ctorElim___redArg(
    mut v_t_458_: *mut leanh::LeanObject,
    mut v_k_459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_458_) {
        0 => {
            let mut v_fvarId_460_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_460_ = leanh::lean_ctor_get(v_t_458_, 0);
            leanh::lean_inc(v_fvarId_460_);
            leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_461_ = leanh::lean_apply_1(v_k_459_, v_fvarId_460_);
            return v___x_461_;
        }
        1 => {
            let mut v_mvarId_462_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_mvarId_462_ = leanh::lean_ctor_get(v_t_458_, 0);
            leanh::lean_inc(v_mvarId_462_);
            leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_463_ = leanh::lean_apply_1(v_k_459_, v_mvarId_462_);
            return v___x_463_;
        }
        2 => {
            let mut v_constName_464_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_constName_464_ = leanh::lean_ctor_get(v_t_458_, 0);
            leanh::lean_inc(v_constName_464_);
            leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_465_ = leanh::lean_apply_1(v_k_459_, v_constName_464_);
            return v___x_465_;
        }
        3 => {
            let mut v_structName_466_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_467_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_structName_466_ = leanh::lean_ctor_get(v_t_458_, 0);
            leanh::lean_inc(v_structName_466_);
            v_idx_467_ = leanh::lean_ctor_get(v_t_458_, 1);
            leanh::lean_inc(v_idx_467_);
            leanh::lean_dec_ref_known(v_t_458_, 2);
            v___x_468_ = leanh::lean_apply_2(v_k_459_, v_structName_466_, v_idx_467_);
            return v___x_468_;
        }
        4 => {
            let mut v_litVal_469_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_litVal_469_ = leanh::lean_ctor_get(v_t_458_, 0);
            leanh::lean_inc_ref(v_litVal_469_);
            leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_470_ = leanh::lean_apply_1(v_k_459_, v_litVal_469_);
            return v___x_470_;
        }
        _ => {
            leanh::lean_dec(v_t_458_);
            return v_k_459_;
        }
    }
}
pub unsafe fn l_Lean_HeadIndex_ctorElim(
    mut v_motive_471_: *mut leanh::LeanObject,
    mut v_ctorIdx_472_: *mut leanh::LeanObject,
    mut v_t_473_: *mut leanh::LeanObject,
    mut v_h_474_: *mut leanh::LeanObject,
    mut v_k_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_473_, v_k_475_);
    return v___x_476_;
}
pub unsafe fn l_Lean_HeadIndex_ctorElim___boxed(
    mut v_motive_477_: *mut leanh::LeanObject,
    mut v_ctorIdx_478_: *mut leanh::LeanObject,
    mut v_t_479_: *mut leanh::LeanObject,
    mut v_h_480_: *mut leanh::LeanObject,
    mut v_k_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ =
        l_Lean_HeadIndex_ctorElim(v_motive_477_, v_ctorIdx_478_, v_t_479_, v_h_480_, v_k_481_);
    leanh::lean_dec(v_ctorIdx_478_);
    return v_res_482_;
}
pub unsafe fn l_Lean_HeadIndex_fvar_elim___redArg(
    mut v_t_483_: *mut leanh::LeanObject,
    mut v_fvar_484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_483_, v_fvar_484_);
    return v___x_485_;
}
pub unsafe fn l_Lean_HeadIndex_fvar_elim(
    mut v_motive_486_: *mut leanh::LeanObject,
    mut v_t_487_: *mut leanh::LeanObject,
    mut v_h_488_: *mut leanh::LeanObject,
    mut v_fvar_489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_487_, v_fvar_489_);
    return v___x_490_;
}
pub unsafe fn l_Lean_HeadIndex_mvar_elim___redArg(
    mut v_t_491_: *mut leanh::LeanObject,
    mut v_mvar_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_491_, v_mvar_492_);
    return v___x_493_;
}
pub unsafe fn l_Lean_HeadIndex_mvar_elim(
    mut v_motive_494_: *mut leanh::LeanObject,
    mut v_t_495_: *mut leanh::LeanObject,
    mut v_h_496_: *mut leanh::LeanObject,
    mut v_mvar_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_495_, v_mvar_497_);
    return v___x_498_;
}
pub unsafe fn l_Lean_HeadIndex_const_elim___redArg(
    mut v_t_499_: *mut leanh::LeanObject,
    mut v_const_500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_501_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_499_, v_const_500_);
    return v___x_501_;
}
pub unsafe fn l_Lean_HeadIndex_const_elim(
    mut v_motive_502_: *mut leanh::LeanObject,
    mut v_t_503_: *mut leanh::LeanObject,
    mut v_h_504_: *mut leanh::LeanObject,
    mut v_const_505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_503_, v_const_505_);
    return v___x_506_;
}
pub unsafe fn l_Lean_HeadIndex_proj_elim___redArg(
    mut v_t_507_: *mut leanh::LeanObject,
    mut v_proj_508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_509_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_507_, v_proj_508_);
    return v___x_509_;
}
pub unsafe fn l_Lean_HeadIndex_proj_elim(
    mut v_motive_510_: *mut leanh::LeanObject,
    mut v_t_511_: *mut leanh::LeanObject,
    mut v_h_512_: *mut leanh::LeanObject,
    mut v_proj_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_511_, v_proj_513_);
    return v___x_514_;
}
pub unsafe fn l_Lean_HeadIndex_lit_elim___redArg(
    mut v_t_515_: *mut leanh::LeanObject,
    mut v_lit_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_515_, v_lit_516_);
    return v___x_517_;
}
pub unsafe fn l_Lean_HeadIndex_lit_elim(
    mut v_motive_518_: *mut leanh::LeanObject,
    mut v_t_519_: *mut leanh::LeanObject,
    mut v_h_520_: *mut leanh::LeanObject,
    mut v_lit_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_519_, v_lit_521_);
    return v___x_522_;
}
pub unsafe fn l_Lean_HeadIndex_sort_elim___redArg(
    mut v_t_523_: *mut leanh::LeanObject,
    mut v_sort_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_523_, v_sort_524_);
    return v___x_525_;
}
pub unsafe fn l_Lean_HeadIndex_sort_elim(
    mut v_motive_526_: *mut leanh::LeanObject,
    mut v_t_527_: *mut leanh::LeanObject,
    mut v_h_528_: *mut leanh::LeanObject,
    mut v_sort_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_527_, v_sort_529_);
    return v___x_530_;
}
pub unsafe fn l_Lean_HeadIndex_lam_elim___redArg(
    mut v_t_531_: *mut leanh::LeanObject,
    mut v_lam_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_531_, v_lam_532_);
    return v___x_533_;
}
pub unsafe fn l_Lean_HeadIndex_lam_elim(
    mut v_motive_534_: *mut leanh::LeanObject,
    mut v_t_535_: *mut leanh::LeanObject,
    mut v_h_536_: *mut leanh::LeanObject,
    mut v_lam_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_535_, v_lam_537_);
    return v___x_538_;
}
pub unsafe fn l_Lean_HeadIndex_forallE_elim___redArg(
    mut v_t_539_: *mut leanh::LeanObject,
    mut v_forallE_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_539_, v_forallE_540_);
    return v___x_541_;
}
pub unsafe fn l_Lean_HeadIndex_forallE_elim(
    mut v_motive_542_: *mut leanh::LeanObject,
    mut v_t_543_: *mut leanh::LeanObject,
    mut v_h_544_: *mut leanh::LeanObject,
    mut v_forallE_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_543_, v_forallE_545_);
    return v___x_546_;
}
pub unsafe fn l_Lean_instBEqHeadIndex_beq(
    mut v_x_551_: *mut leanh::LeanObject,
    mut v_x_552_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_551_) {
        0 => {
            if leanh::lean_obj_tag(v_x_552_) == 0 {
                let mut v_fvarId_553_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_fvarId_554_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_555_: u8 = 0;
                v_fvarId_553_ = leanh::lean_ctor_get(v_x_551_, 0);
                v_fvarId_554_ = leanh::lean_ctor_get(v_x_552_, 0);
                v___x_555_ = l_Lean_instBEqFVarId_beq(v_fvarId_553_, v_fvarId_554_);
                return v___x_555_;
            } else {
                let mut v___x_556_: u8 = 0;
                v___x_556_ = 0;
                return v___x_556_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_552_) == 1 {
                let mut v_mvarId_557_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_mvarId_558_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_559_: u8 = 0;
                v_mvarId_557_ = leanh::lean_ctor_get(v_x_551_, 0);
                v_mvarId_558_ = leanh::lean_ctor_get(v_x_552_, 0);
                v___x_559_ = l_Lean_instBEqMVarId_beq(v_mvarId_557_, v_mvarId_558_);
                return v___x_559_;
            } else {
                let mut v___x_560_: u8 = 0;
                v___x_560_ = 0;
                return v___x_560_;
            }
        }
        2 => {
            if leanh::lean_obj_tag(v_x_552_) == 2 {
                let mut v_constName_561_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_constName_562_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_563_: u8 = 0;
                v_constName_561_ = leanh::lean_ctor_get(v_x_551_, 0);
                v_constName_562_ = leanh::lean_ctor_get(v_x_552_, 0);
                v___x_563_ = lean_name_eq(v_constName_561_, v_constName_562_);
                return v___x_563_;
            } else {
                let mut v___x_564_: u8 = 0;
                v___x_564_ = 0;
                return v___x_564_;
            }
        }
        3 => {
            if leanh::lean_obj_tag(v_x_552_) == 3 {
                let mut v_structName_565_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_idx_566_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_structName_567_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_idx_568_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_569_: u8 = 0;
                v_structName_565_ = leanh::lean_ctor_get(v_x_551_, 0);
                v_idx_566_ = leanh::lean_ctor_get(v_x_551_, 1);
                v_structName_567_ = leanh::lean_ctor_get(v_x_552_, 0);
                v_idx_568_ = leanh::lean_ctor_get(v_x_552_, 1);
                v___x_569_ = lean_name_eq(v_structName_565_, v_structName_567_);
                if v___x_569_ == 0 {
                    return v___x_569_;
                } else {
                    let mut v___x_570_: u8 = 0;
                    v___x_570_ = lean_nat_dec_eq(v_idx_566_, v_idx_568_);
                    return v___x_570_;
                }
            } else {
                let mut v___x_571_: u8 = 0;
                v___x_571_ = 0;
                return v___x_571_;
            }
        }
        4 => {
            if leanh::lean_obj_tag(v_x_552_) == 4 {
                let mut v_litVal_572_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_litVal_573_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_574_: u8 = 0;
                v_litVal_572_ = leanh::lean_ctor_get(v_x_551_, 0);
                v_litVal_573_ = leanh::lean_ctor_get(v_x_552_, 0);
                v___x_574_ = l_Lean_instBEqLiteral_beq(v_litVal_572_, v_litVal_573_);
                return v___x_574_;
            } else {
                let mut v___x_575_: u8 = 0;
                v___x_575_ = 0;
                return v___x_575_;
            }
        }
        5 => {
            if leanh::lean_obj_tag(v_x_552_) == 5 {
                let mut v___x_576_: u8 = 0;
                v___x_576_ = 1;
                return v___x_576_;
            } else {
                let mut v___x_577_: u8 = 0;
                v___x_577_ = 0;
                return v___x_577_;
            }
        }
        6 => {
            if leanh::lean_obj_tag(v_x_552_) == 6 {
                let mut v___x_578_: u8 = 0;
                v___x_578_ = 1;
                return v___x_578_;
            } else {
                let mut v___x_579_: u8 = 0;
                v___x_579_ = 0;
                return v___x_579_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_552_) == 7 {
                let mut v___x_580_: u8 = 0;
                v___x_580_ = 1;
                return v___x_580_;
            } else {
                let mut v___x_581_: u8 = 0;
                v___x_581_ = 0;
                return v___x_581_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqHeadIndex_beq___boxed(
    mut v_x_582_: *mut leanh::LeanObject,
    mut v_x_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_584_: u8 = 0;
    let mut v_r_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_instBEqHeadIndex_beq(v_x_582_, v_x_583_);
    leanh::lean_dec(v_x_583_);
    leanh::lean_dec(v_x_582_);
    v_r_585_ = leanh::lean_box((v_res_584_) as usize);
    return v_r_585_;
}
pub unsafe fn _init_l_Lean_instReprHeadIndex_repr___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = leanh::lean_unsigned_to_nat(2);
    v___x_604_ = lean_nat_to_int(v___x_603_);
    return v___x_604_;
}
pub unsafe fn _init_l_Lean_instReprHeadIndex_repr___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_605_ = leanh::lean_unsigned_to_nat(1);
    v___x_606_ = lean_nat_to_int(v___x_605_);
    return v___x_606_;
}
pub unsafe fn l_Lean_instReprHeadIndex_repr(
    mut v_x_631_: *mut leanh::LeanObject,
    mut v_prec_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: u8 = 0;
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_constName_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: u8 = 0;
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___y_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_litVal_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_631_) {
                0 => {
                    v_fvarId_654_ = leanh::lean_ctor_get(v_x_631_, 0);
                    leanh::lean_inc(v_fvarId_654_);
                    leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_665_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_666_ = lean_nat_dec_le(v___x_665_, v_prec_632_);
                    if v___x_666_ == 0 {
                        v___x_667_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_656_ = v___x_667_;
                        state = 4;
                        continue;
                    } else {
                        v___x_668_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprHeadIndex_repr___closed__10_once
                            ),
                            _init_l_Lean_instReprHeadIndex_repr___closed__10,
                        );
                        v___y_656_ = v___x_668_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v_mvarId_669_ = leanh::lean_ctor_get(v_x_631_, 0);
                    leanh::lean_inc(v_mvarId_669_);
                    leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_680_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_681_ = lean_nat_dec_le(v___x_680_, v_prec_632_);
                    if v___x_681_ == 0 {
                        v___x_682_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_671_ = v___x_682_;
                        state = 5;
                        continue;
                    } else {
                        v___x_683_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprHeadIndex_repr___closed__10_once
                            ),
                            _init_l_Lean_instReprHeadIndex_repr___closed__10,
                        );
                        v___y_671_ = v___x_683_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_constName_684_ = leanh::lean_ctor_get(v_x_631_, 0);
                    leanh::lean_inc(v_constName_684_);
                    leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_695_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_696_ = lean_nat_dec_le(v___x_695_, v_prec_632_);
                    if v___x_696_ == 0 {
                        v___x_697_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_686_ = v___x_697_;
                        state = 6;
                        continue;
                    } else {
                        v___x_698_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprHeadIndex_repr___closed__10_once
                            ),
                            _init_l_Lean_instReprHeadIndex_repr___closed__10,
                        );
                        v___y_686_ = v___x_698_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    v_structName_699_ = leanh::lean_ctor_get(v_x_631_, 0);
                    v_idx_700_ = leanh::lean_ctor_get(v_x_631_, 1);
                    v_isSharedCheck_725_ = (!leanh::lean_is_exclusive(v_x_631_)) as u8;
                    if v_isSharedCheck_725_ == 0 {
                        v___x_702_ = v_x_631_;
                        v_isShared_703_ = v_isSharedCheck_725_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_idx_700_);
                        leanh::lean_inc(v_structName_699_);
                        leanh::lean_dec(v_x_631_);
                        v___x_702_ = leanh::lean_box(0);
                        v_isShared_703_ = v_isSharedCheck_725_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_litVal_726_ = leanh::lean_ctor_get(v_x_631_, 0);
                    leanh::lean_inc_ref(v_litVal_726_);
                    leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_737_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_738_ = lean_nat_dec_le(v___x_737_, v_prec_632_);
                    if v___x_738_ == 0 {
                        v___x_739_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_728_ = v___x_739_;
                        state = 10;
                        continue;
                    } else {
                        v___x_740_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprHeadIndex_repr___closed__10_once
                            ),
                            _init_l_Lean_instReprHeadIndex_repr___closed__10,
                        );
                        v___y_728_ = v___x_740_;
                        state = 10;
                        continue;
                    }
                }
                5 => {
                    v___x_741_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_742_ = lean_nat_dec_le(v___x_741_, v_prec_632_);
                    if v___x_742_ == 0 {
                        v___x_743_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_634_ = v___x_743_;
                        state = 1;
                        continue;
                    } else {
                        v___x_744_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprHeadIndex_repr___closed__10_once
                            ),
                            _init_l_Lean_instReprHeadIndex_repr___closed__10,
                        );
                        v___y_634_ = v___x_744_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v___x_745_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_746_ = lean_nat_dec_le(v___x_745_, v_prec_632_);
                    if v___x_746_ == 0 {
                        v___x_747_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_641_ = v___x_747_;
                        state = 2;
                        continue;
                    } else {
                        v___x_748_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprHeadIndex_repr___closed__10_once
                            ),
                            _init_l_Lean_instReprHeadIndex_repr___closed__10,
                        );
                        v___y_641_ = v___x_748_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_749_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_750_ = lean_nat_dec_le(v___x_749_, v_prec_632_);
                    if v___x_750_ == 0 {
                        v___x_751_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_648_ = v___x_751_;
                        state = 3;
                        continue;
                    } else {
                        v___x_752_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprHeadIndex_repr___closed__10_once
                            ),
                            _init_l_Lean_instReprHeadIndex_repr___closed__10,
                        );
                        v___y_648_ = v___x_752_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_635_ = l_Lean_instReprHeadIndex_repr___closed__1;
                leanh::lean_inc(v___y_634_);
                v___x_636_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_636_, 0, v___y_634_);
                leanh::lean_ctor_set(v___x_636_, 1, v___x_635_);
                v___x_637_ = 0;
                v___x_638_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_638_, 0, v___x_636_);
                leanh::lean_ctor_set_uint8(
                    v___x_638_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_637_,
                );
                v___x_639_ = l_Repr_addAppParen(v___x_638_, v_prec_632_);
                return v___x_639_;
            }
            2 => {
                v___x_642_ = l_Lean_instReprHeadIndex_repr___closed__3;
                leanh::lean_inc(v___y_641_);
                v___x_643_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_643_, 0, v___y_641_);
                leanh::lean_ctor_set(v___x_643_, 1, v___x_642_);
                v___x_644_ = 0;
                v___x_645_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_645_, 0, v___x_643_);
                leanh::lean_ctor_set_uint8(
                    v___x_645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_644_,
                );
                v___x_646_ = l_Repr_addAppParen(v___x_645_, v_prec_632_);
                return v___x_646_;
            }
            3 => {
                v___x_649_ = l_Lean_instReprHeadIndex_repr___closed__5;
                leanh::lean_inc(v___y_648_);
                v___x_650_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_650_, 0, v___y_648_);
                leanh::lean_ctor_set(v___x_650_, 1, v___x_649_);
                v___x_651_ = 0;
                v___x_652_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_652_, 0, v___x_650_);
                leanh::lean_ctor_set_uint8(
                    v___x_652_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                v___x_653_ = l_Repr_addAppParen(v___x_652_, v_prec_632_);
                return v___x_653_;
            }
            4 => {
                v___x_657_ = l_Lean_instReprHeadIndex_repr___closed__8;
                v___x_658_ = leanh::lean_unsigned_to_nat(1024);
                v___x_659_ = l_Lean_Name_reprPrec(v_fvarId_654_, v___x_658_);
                v___x_660_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_660_, 0, v___x_657_);
                leanh::lean_ctor_set(v___x_660_, 1, v___x_659_);
                leanh::lean_inc(v___y_656_);
                v___x_661_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_661_, 0, v___y_656_);
                leanh::lean_ctor_set(v___x_661_, 1, v___x_660_);
                v___x_662_ = 0;
                v___x_663_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_663_, 0, v___x_661_);
                leanh::lean_ctor_set_uint8(
                    v___x_663_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_662_,
                );
                v___x_664_ = l_Repr_addAppParen(v___x_663_, v_prec_632_);
                return v___x_664_;
            }
            5 => {
                v___x_672_ = l_Lean_instReprHeadIndex_repr___closed__13;
                v___x_673_ = leanh::lean_unsigned_to_nat(1024);
                v___x_674_ = l_Lean_Name_reprPrec(v_mvarId_669_, v___x_673_);
                v___x_675_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_675_, 0, v___x_672_);
                leanh::lean_ctor_set(v___x_675_, 1, v___x_674_);
                leanh::lean_inc(v___y_671_);
                v___x_676_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_676_, 0, v___y_671_);
                leanh::lean_ctor_set(v___x_676_, 1, v___x_675_);
                v___x_677_ = 0;
                v___x_678_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_678_, 0, v___x_676_);
                leanh::lean_ctor_set_uint8(
                    v___x_678_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_677_,
                );
                v___x_679_ = l_Repr_addAppParen(v___x_678_, v_prec_632_);
                return v___x_679_;
            }
            6 => {
                v___x_687_ = l_Lean_instReprHeadIndex_repr___closed__16;
                v___x_688_ = leanh::lean_unsigned_to_nat(1024);
                v___x_689_ = l_Lean_Name_reprPrec(v_constName_684_, v___x_688_);
                v___x_690_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_690_, 0, v___x_687_);
                leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
                leanh::lean_inc(v___y_686_);
                v___x_691_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_691_, 0, v___y_686_);
                leanh::lean_ctor_set(v___x_691_, 1, v___x_690_);
                v___x_692_ = 0;
                v___x_693_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_693_, 0, v___x_691_);
                leanh::lean_ctor_set_uint8(
                    v___x_693_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_692_,
                );
                v___x_694_ = l_Repr_addAppParen(v___x_693_, v_prec_632_);
                return v___x_694_;
            }
            7 => {
                v___x_721_ = leanh::lean_unsigned_to_nat(1024);
                v___x_722_ = lean_nat_dec_le(v___x_721_, v_prec_632_);
                if v___x_722_ == 0 {
                    v___x_723_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                        _init_l_Lean_instReprHeadIndex_repr___closed__9,
                    );
                    v___y_705_ = v___x_723_;
                    state = 8;
                    continue;
                } else {
                    v___x_724_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10),
                        core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__10_once),
                        _init_l_Lean_instReprHeadIndex_repr___closed__10,
                    );
                    v___y_705_ = v___x_724_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_706_ = leanh::lean_box(1);
                v___x_707_ = l_Lean_instReprHeadIndex_repr___closed__19;
                v___x_708_ = leanh::lean_unsigned_to_nat(1024);
                v___x_709_ = l_Lean_Name_reprPrec(v_structName_699_, v___x_708_);
                if v_isShared_703_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_702_, 5);
                    leanh::lean_ctor_set(v___x_702_, 1, v___x_709_);
                    leanh::lean_ctor_set(v___x_702_, 0, v___x_707_);
                    v___x_711_ = v___x_702_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_720_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_707_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_709_);
                    v___x_711_ = v_reuseFailAlloc_720_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_712_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_712_, 0, v___x_711_);
                leanh::lean_ctor_set(v___x_712_, 1, v___x_706_);
                v___x_713_ = l_Nat_reprFast(v_idx_700_);
                v___x_714_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_714_, 0, v___x_713_);
                v___x_715_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_715_, 0, v___x_712_);
                leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
                leanh::lean_inc(v___y_705_);
                v___x_716_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_716_, 0, v___y_705_);
                leanh::lean_ctor_set(v___x_716_, 1, v___x_715_);
                v___x_717_ = 0;
                v___x_718_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_718_, 0, v___x_716_);
                leanh::lean_ctor_set_uint8(
                    v___x_718_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_717_,
                );
                v___x_719_ = l_Repr_addAppParen(v___x_718_, v_prec_632_);
                return v___x_719_;
            }
            10 => {
                v___x_729_ = l_Lean_instReprHeadIndex_repr___closed__22;
                v___x_730_ = leanh::lean_unsigned_to_nat(1024);
                v___x_731_ = l_Lean_instReprLiteral_repr(v_litVal_726_, v___x_730_);
                v___x_732_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_732_, 0, v___x_729_);
                leanh::lean_ctor_set(v___x_732_, 1, v___x_731_);
                leanh::lean_inc(v___y_728_);
                v___x_733_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_733_, 0, v___y_728_);
                leanh::lean_ctor_set(v___x_733_, 1, v___x_732_);
                v___x_734_ = 0;
                v___x_735_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_735_, 0, v___x_733_);
                leanh::lean_ctor_set_uint8(
                    v___x_735_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_734_,
                );
                v___x_736_ = l_Repr_addAppParen(v___x_735_, v_prec_632_);
                return v___x_736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprHeadIndex_repr___boxed(
    mut v_x_753_: *mut leanh::LeanObject,
    mut v_prec_754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_755_ = l_Lean_instReprHeadIndex_repr(v_x_753_, v_prec_754_);
    leanh::lean_dec(v_prec_754_);
    return v_res_755_;
}
pub unsafe fn _init_l_Lean_HeadIndex_hash___closed__0() -> u64 {
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u64 = 0;
    v___x_758_ = leanh::lean_unsigned_to_nat(1723);
    v___x_759_ = lean_uint64_of_nat(v___x_758_);
    return v___x_759_;
}
pub unsafe fn _init_l_Lean_HeadIndex_hash___closed__1() -> u64 {
    let mut v___x_760_: u64 = 0;
    let mut v___x_761_: u64 = 0;
    let mut v___x_762_: u64 = 0;
    v___x_760_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0_once),
        _init_l_Lean_HeadIndex_hash___closed__0,
    );
    v___x_761_ = 17u64;
    v___x_762_ = lean_uint64_mix_hash(v___x_761_, v___x_760_);
    return v___x_762_;
}
pub unsafe fn l_Lean_HeadIndex_hash(mut v_x_763_: *mut leanh::LeanObject) -> u64 {
    let mut v_fvarId_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u64 = 0;
    let mut v___x_766_: u64 = 0;
    let mut v___x_767_: u64 = 0;
    let mut v_mvarId_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: u64 = 0;
    let mut v___x_770_: u64 = 0;
    let mut v___x_771_: u64 = 0;
    let mut v_constName_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: u64 = 0;
    let mut v___x_774_: u64 = 0;
    let mut v_hash_775_: u64 = 0;
    let mut v___x_776_: u64 = 0;
    let mut v_structName_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u64 = 0;
    let mut v___y_781_: u64 = 0;
    let mut v___x_782_: u64 = 0;
    let mut v___x_783_: u64 = 0;
    let mut v___x_784_: u64 = 0;
    let mut v___x_785_: u64 = 0;
    let mut v_hash_786_: u64 = 0;
    let mut v_litVal_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: u64 = 0;
    let mut v___x_789_: u64 = 0;
    let mut v___x_790_: u64 = 0;
    let mut v___x_791_: u64 = 0;
    let mut v___x_792_: u64 = 0;
    let mut v___x_793_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_763_) {
                0 => {
                    v_fvarId_764_ = leanh::lean_ctor_get(v_x_763_, 0);
                    v___x_765_ = 11u64;
                    v___x_766_ = l_Lean_instHashableFVarId_hash(v_fvarId_764_);
                    v___x_767_ = lean_uint64_mix_hash(v___x_765_, v___x_766_);
                    return v___x_767_;
                }
                1 => {
                    v_mvarId_768_ = leanh::lean_ctor_get(v_x_763_, 0);
                    v___x_769_ = 13u64;
                    v___x_770_ = l_Lean_instHashableMVarId_hash(v_mvarId_768_);
                    v___x_771_ = lean_uint64_mix_hash(v___x_769_, v___x_770_);
                    return v___x_771_;
                }
                2 => {
                    v_constName_772_ = leanh::lean_ctor_get(v_x_763_, 0);
                    v___x_773_ = 17u64;
                    if leanh::lean_obj_tag(v_constName_772_) == 0 {
                        v___x_774_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__1_once),
                            _init_l_Lean_HeadIndex_hash___closed__1,
                        );
                        return v___x_774_;
                    } else {
                        v_hash_775_ = leanh::lean_ctor_get_uint64(
                            v_constName_772_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_776_ = lean_uint64_mix_hash(v___x_773_, v_hash_775_);
                        return v___x_776_;
                    }
                }
                3 => {
                    v_structName_777_ = leanh::lean_ctor_get(v_x_763_, 0);
                    v_idx_778_ = leanh::lean_ctor_get(v_x_763_, 1);
                    v___x_779_ = 19u64;
                    if leanh::lean_obj_tag(v_structName_777_) == 0 {
                        v___x_785_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0_once),
                            _init_l_Lean_HeadIndex_hash___closed__0,
                        );
                        v___y_781_ = v___x_785_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_786_ = leanh::lean_ctor_get_uint64(
                            v_structName_777_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_781_ = v_hash_786_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_litVal_787_ = leanh::lean_ctor_get(v_x_763_, 0);
                    v___x_788_ = 23u64;
                    v___x_789_ = l_Lean_Literal_hash(v_litVal_787_);
                    v___x_790_ = lean_uint64_mix_hash(v___x_788_, v___x_789_);
                    return v___x_790_;
                }
                5 => {
                    v___x_791_ = 29u64;
                    return v___x_791_;
                }
                6 => {
                    v___x_792_ = 31u64;
                    return v___x_792_;
                }
                _ => {
                    v___x_793_ = 37u64;
                    return v___x_793_;
                }
            },
            1 => {
                v___x_782_ = lean_uint64_of_nat(v_idx_778_);
                v___x_783_ = lean_uint64_mix_hash(v___y_781_, v___x_782_);
                v___x_784_ = lean_uint64_mix_hash(v___x_779_, v___x_783_);
                return v___x_784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_HeadIndex_hash___boxed(
    mut v_x_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_795_: u64 = 0;
    let mut v_r_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_HeadIndex_hash(v_x_794_);
    leanh::lean_dec(v_x_794_);
    v_r_796_ = leanh::lean_box_uint64(v_res_795_);
    return v_r_796_;
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(
    mut v_a_799_: *mut leanh::LeanObject,
    mut v_a_800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_799_) {
                5 => {
                    v_fn_801_ = leanh::lean_ctor_get(v_a_799_, 0);
                    v___x_802_ = leanh::lean_unsigned_to_nat(1);
                    v___x_803_ = lean_nat_add(v_a_800_, v___x_802_);
                    leanh::lean_dec(v_a_800_);
                    v_a_799_ = v_fn_801_;
                    v_a_800_ = v___x_803_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_body_805_ = leanh::lean_ctor_get(v_a_799_, 3);
                    v_a_799_ = v_body_805_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_807_ = leanh::lean_ctor_get(v_a_799_, 1);
                    v_a_799_ = v_expr_807_;
                    state = 0;
                    continue;
                }
                _ => {
                    return v_a_800_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go___boxed(
    mut v_a_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_a_809_, v_a_810_);
    leanh::lean_dec_ref(v_a_809_);
    return v_res_811_;
}
pub unsafe fn l_Lean_Expr_headNumArgs(
    mut v_e_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = leanh::lean_unsigned_to_nat(0);
    v___x_814_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_e_812_, v___x_813_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Expr_headNumArgs___boxed(
    mut v_e_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Expr_headNumArgs(v_e_815_);
    leanh::lean_dec_ref(v_e_815_);
    return v_res_816_;
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(
    mut v_x_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvarId_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_x_823_) {
                    2 => {
                        v_mvarId_824_ = leanh::lean_ctor_get(v_x_823_, 0);
                        leanh::lean_inc(v_mvarId_824_);
                        v___x_825_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_825_, 0, v_mvarId_824_);
                        v___x_826_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_826_, 0, v___x_825_);
                        return v___x_826_;
                    }
                    1 => {
                        v_fvarId_827_ = leanh::lean_ctor_get(v_x_823_, 0);
                        leanh::lean_inc(v_fvarId_827_);
                        v___x_828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_828_, 0, v_fvarId_827_);
                        v___x_829_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_829_, 0, v___x_828_);
                        return v___x_829_;
                    }
                    4 => {
                        v_declName_830_ = leanh::lean_ctor_get(v_x_823_, 0);
                        leanh::lean_inc(v_declName_830_);
                        v___x_831_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_831_, 0, v_declName_830_);
                        v___x_832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_832_, 0, v___x_831_);
                        return v___x_832_;
                    }
                    11 => {
                        v_typeName_833_ = leanh::lean_ctor_get(v_x_823_, 0);
                        v_idx_834_ = leanh::lean_ctor_get(v_x_823_, 1);
                        leanh::lean_inc(v_idx_834_);
                        leanh::lean_inc(v_typeName_833_);
                        v___x_835_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_835_, 0, v_typeName_833_);
                        leanh::lean_ctor_set(v___x_835_, 1, v_idx_834_);
                        v___x_836_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_836_, 0, v___x_835_);
                        return v___x_836_;
                    }
                    3 => {
                        v___x_837_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0;
                        return v___x_837_;
                    }
                    6 => {
                        v___x_838_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1;
                        return v___x_838_;
                    }
                    7 => {
                        v___x_839_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2;
                        return v___x_839_;
                    }
                    9 => {
                        v_a_840_ = leanh::lean_ctor_get(v_x_823_, 0);
                        leanh::lean_inc_ref(v_a_840_);
                        v___x_841_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_841_, 0, v_a_840_);
                        v___x_842_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_842_, 0, v___x_841_);
                        return v___x_842_;
                    }
                    5 => {
                        v_fn_843_ = leanh::lean_ctor_get(v_x_823_, 0);
                        v_x_823_ = v_fn_843_;
                        state = 0;
                        continue;
                    }
                    8 => {
                        v_body_845_ = leanh::lean_ctor_get(v_x_823_, 3);
                        v_x_823_ = v_body_845_;
                        state = 0;
                        continue;
                    }
                    10 => {
                        v_expr_847_ = leanh::lean_ctor_get(v_x_823_, 1);
                        v_x_823_ = v_expr_847_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        v___x_849_ = leanh::lean_box(0);
                        return v___x_849_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(
    mut v_x_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_851_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_x_850_);
    leanh::lean_dec_ref(v_x_850_);
    return v_res_851_;
}
pub unsafe fn l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(
    mut v_msg_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = l_Lean_instInhabitedHeadIndex_default;
    v___x_854_ = lean_panic_fn_borrowed(v___x_853_, v_msg_852_);
    return v___x_854_;
}
pub unsafe fn _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2;
    v___x_859_ = leanh::lean_unsigned_to_nat(31);
    v___x_860_ = leanh::lean_unsigned_to_nat(104);
    v___x_861_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1;
    v___x_862_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0;
    v___x_863_ =
        l_mkPanicMessageWithDecl(v___x_862_, v___x_861_, v___x_860_, v___x_859_, v___x_858_);
    return v___x_863_;
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(
    mut v_x_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvarId_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_864_) {
                2 => {
                    v_mvarId_865_ = leanh::lean_ctor_get(v_x_864_, 0);
                    leanh::lean_inc(v_mvarId_865_);
                    leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_866_, 0, v_mvarId_865_);
                    return v___x_866_;
                }
                1 => {
                    v_fvarId_867_ = leanh::lean_ctor_get(v_x_864_, 0);
                    leanh::lean_inc(v_fvarId_867_);
                    leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_868_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_868_, 0, v_fvarId_867_);
                    return v___x_868_;
                }
                4 => {
                    v_declName_869_ = leanh::lean_ctor_get(v_x_864_, 0);
                    leanh::lean_inc(v_declName_869_);
                    leanh::lean_dec_ref_known(v_x_864_, 2);
                    v___x_870_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_870_, 0, v_declName_869_);
                    return v___x_870_;
                }
                11 => {
                    v_typeName_871_ = leanh::lean_ctor_get(v_x_864_, 0);
                    leanh::lean_inc(v_typeName_871_);
                    v_idx_872_ = leanh::lean_ctor_get(v_x_864_, 1);
                    leanh::lean_inc(v_idx_872_);
                    leanh::lean_dec_ref_known(v_x_864_, 3);
                    v___x_873_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_873_, 0, v_typeName_871_);
                    leanh::lean_ctor_set(v___x_873_, 1, v_idx_872_);
                    return v___x_873_;
                }
                3 => {
                    leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_874_ = leanh::lean_box(5);
                    return v___x_874_;
                }
                6 => {
                    leanh::lean_dec_ref_known(v_x_864_, 3);
                    v___x_875_ = leanh::lean_box(6);
                    return v___x_875_;
                }
                7 => {
                    leanh::lean_dec_ref_known(v_x_864_, 3);
                    v___x_876_ = leanh::lean_box(7);
                    return v___x_876_;
                }
                9 => {
                    v_a_877_ = leanh::lean_ctor_get(v_x_864_, 0);
                    leanh::lean_inc_ref(v_a_877_);
                    leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_878_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_878_, 0, v_a_877_);
                    return v___x_878_;
                }
                5 => {
                    v_fn_879_ = leanh::lean_ctor_get(v_x_864_, 0);
                    leanh::lean_inc_ref(v_fn_879_);
                    leanh::lean_dec_ref_known(v_x_864_, 2);
                    v_x_864_ = v_fn_879_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_value_881_ = leanh::lean_ctor_get(v_x_864_, 2);
                    leanh::lean_inc_ref(v_value_881_);
                    v_body_882_ = leanh::lean_ctor_get(v_x_864_, 3);
                    leanh::lean_inc_ref(v_body_882_);
                    leanh::lean_dec_ref_known(v_x_864_, 4);
                    v___x_883_ = lean_expr_instantiate1(v_body_882_, v_value_881_);
                    leanh::lean_dec_ref(v_value_881_);
                    leanh::lean_dec_ref(v_body_882_);
                    v_x_864_ = v___x_883_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_885_ = leanh::lean_ctor_get(v_x_864_, 1);
                    leanh::lean_inc_ref(v_expr_885_);
                    leanh::lean_dec_ref_known(v_x_864_, 2);
                    v_x_864_ = v_expr_885_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_x_864_);
                    v___x_887_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3), core::ptr::addr_of_mut!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once), _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3);
                    v___x_888_ = l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(v___x_887_);
                    return v___x_888_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_toHeadIndex(
    mut v_e_889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_e_889_);
    if leanh::lean_obj_tag(v___x_890_) == 0 {
        let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_891_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(v_e_889_);
        return v___x_891_;
    } else {
        let mut v_val_892_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_889_);
        v_val_892_ = leanh::lean_ctor_get(v___x_890_, 0);
        leanh::lean_inc(v_val_892_);
        leanh::lean_dec_ref_known(v___x_890_, 1);
        return v_val_892_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_HeadIndex(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_HeadIndex(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_HeadIndex(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_HeadIndex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_HeadIndex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_HeadIndex(builtin);
}