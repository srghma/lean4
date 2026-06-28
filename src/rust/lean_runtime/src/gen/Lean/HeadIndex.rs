// Lean compiler output
// Module: Lean.HeadIndex
// Imports: Lean.Expr
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Literal_hash, l_Lean_instBEqFVarId_beq, l_Lean_instBEqLiteral_beq,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableFVarId_hash, l_Lean_instHashableMVarId_hash,
    l_Lean_instReprLiteral_repr, runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_panic_fn_borrowed,
    lean_uint64_mix_hash, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
pub static l_Lean_instInhabitedHeadIndex_default___closed__0_value: crate::leanh::LeanCtorObject<
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
static mut l_Lean_instInhabitedHeadIndex_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedHeadIndex_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedHeadIndex_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedHeadIndex_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedHeadIndex: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedHeadIndex_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instBEqHeadIndex___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqHeadIndex_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqHeadIndex___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqHeadIndex___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqHeadIndex: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqHeadIndex___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__0_value: crate::leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 115, 111, 114, 116,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__2_value: crate::leanh::LeanStringObject<19> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 108, 97, 109, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__4_value: crate::leanh::LeanStringObject<23> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 102, 111, 114, 97,
            108, 108, 69, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__6_value: crate::leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 102, 118, 97, 114,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprHeadIndex_repr___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprHeadIndex_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprHeadIndex_repr___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprHeadIndex_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprHeadIndex_repr___closed__11_value: crate::leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 109, 118, 97, 114,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__12_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__13_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__12_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__14_value: crate::leanh::LeanStringObject<21> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 99, 111, 110, 115,
            116, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__15_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__16_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__15_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__17_value: crate::leanh::LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 112, 114, 111, 106,
            0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__18_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__17_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__19_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__18_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__20_value: crate::leanh::LeanStringObject<19> =
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
            76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 46, 108, 105, 116, 0,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__21_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex_repr___closed__22_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__21_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprHeadIndex_repr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex_repr___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprHeadIndex___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprHeadIndex_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprHeadIndex___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprHeadIndex: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprHeadIndex___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_HeadIndex_hash___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_HeadIndex_hash___closed__0: u64 = 0;
static mut l_Lean_HeadIndex_hash___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_HeadIndex_hash___closed__1: u64 = 0;
pub static l_Lean_instHashableHeadIndex___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_HeadIndex_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableHeadIndex___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableHeadIndex___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instHashableHeadIndex: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableHeadIndex___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((6 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((7 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 72, 101, 97, 100, 73, 110, 100, 101, 120, 0,
    ],
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value:
    crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_HeadIndex_ctorIdx(
    mut v_x_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_447_) {
        0 => {
            let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_448_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_448_;
        }
        1 => {
            let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_449_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_449_;
        }
        2 => {
            let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_450_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_450_;
        }
        3 => {
            let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_451_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_451_;
        }
        4 => {
            let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_452_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_452_;
        }
        5 => {
            let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_453_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_453_;
        }
        6 => {
            let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_454_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_454_;
        }
        _ => {
            let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_455_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_455_;
        }
    }
}
pub unsafe fn l_Lean_HeadIndex_ctorIdx___boxed(
    mut v_x_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Lean_HeadIndex_ctorIdx(v_x_456_);
    crate::leanh::lean_dec(v_x_456_);
    return v_res_457_;
}
pub unsafe fn l_Lean_HeadIndex_ctorElim___redArg(
    mut v_t_458_: *mut crate::leanh::LeanObject,
    mut v_k_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_458_) {
        0 => {
            let mut v_fvarId_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_460_ = crate::leanh::lean_ctor_get(v_t_458_, 0);
            crate::leanh::lean_inc(v_fvarId_460_);
            crate::leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_461_ = crate::leanh::lean_apply_1(v_k_459_, v_fvarId_460_);
            return v___x_461_;
        }
        1 => {
            let mut v_mvarId_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_mvarId_462_ = crate::leanh::lean_ctor_get(v_t_458_, 0);
            crate::leanh::lean_inc(v_mvarId_462_);
            crate::leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_463_ = crate::leanh::lean_apply_1(v_k_459_, v_mvarId_462_);
            return v___x_463_;
        }
        2 => {
            let mut v_constName_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_constName_464_ = crate::leanh::lean_ctor_get(v_t_458_, 0);
            crate::leanh::lean_inc(v_constName_464_);
            crate::leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_465_ = crate::leanh::lean_apply_1(v_k_459_, v_constName_464_);
            return v___x_465_;
        }
        3 => {
            let mut v_structName_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_structName_466_ = crate::leanh::lean_ctor_get(v_t_458_, 0);
            crate::leanh::lean_inc(v_structName_466_);
            v_idx_467_ = crate::leanh::lean_ctor_get(v_t_458_, 1);
            crate::leanh::lean_inc(v_idx_467_);
            crate::leanh::lean_dec_ref_known(v_t_458_, 2);
            v___x_468_ = crate::leanh::lean_apply_2(v_k_459_, v_structName_466_, v_idx_467_);
            return v___x_468_;
        }
        4 => {
            let mut v_litVal_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_litVal_469_ = crate::leanh::lean_ctor_get(v_t_458_, 0);
            crate::leanh::lean_inc_ref(v_litVal_469_);
            crate::leanh::lean_dec_ref_known(v_t_458_, 1);
            v___x_470_ = crate::leanh::lean_apply_1(v_k_459_, v_litVal_469_);
            return v___x_470_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_458_);
            return v_k_459_;
        }
    }
}
pub unsafe fn l_Lean_HeadIndex_ctorElim(
    mut v_motive_471_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_472_: *mut crate::leanh::LeanObject,
    mut v_t_473_: *mut crate::leanh::LeanObject,
    mut v_h_474_: *mut crate::leanh::LeanObject,
    mut v_k_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_473_, v_k_475_);
    return v___x_476_;
}
pub unsafe fn l_Lean_HeadIndex_ctorElim___boxed(
    mut v_motive_477_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_478_: *mut crate::leanh::LeanObject,
    mut v_t_479_: *mut crate::leanh::LeanObject,
    mut v_h_480_: *mut crate::leanh::LeanObject,
    mut v_k_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ =
        l_Lean_HeadIndex_ctorElim(v_motive_477_, v_ctorIdx_478_, v_t_479_, v_h_480_, v_k_481_);
    crate::leanh::lean_dec(v_ctorIdx_478_);
    return v_res_482_;
}
pub unsafe fn l_Lean_HeadIndex_fvar_elim___redArg(
    mut v_t_483_: *mut crate::leanh::LeanObject,
    mut v_fvar_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_483_, v_fvar_484_);
    return v___x_485_;
}
pub unsafe fn l_Lean_HeadIndex_fvar_elim(
    mut v_motive_486_: *mut crate::leanh::LeanObject,
    mut v_t_487_: *mut crate::leanh::LeanObject,
    mut v_h_488_: *mut crate::leanh::LeanObject,
    mut v_fvar_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_487_, v_fvar_489_);
    return v___x_490_;
}
pub unsafe fn l_Lean_HeadIndex_mvar_elim___redArg(
    mut v_t_491_: *mut crate::leanh::LeanObject,
    mut v_mvar_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_491_, v_mvar_492_);
    return v___x_493_;
}
pub unsafe fn l_Lean_HeadIndex_mvar_elim(
    mut v_motive_494_: *mut crate::leanh::LeanObject,
    mut v_t_495_: *mut crate::leanh::LeanObject,
    mut v_h_496_: *mut crate::leanh::LeanObject,
    mut v_mvar_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_495_, v_mvar_497_);
    return v___x_498_;
}
pub unsafe fn l_Lean_HeadIndex_const_elim___redArg(
    mut v_t_499_: *mut crate::leanh::LeanObject,
    mut v_const_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_501_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_499_, v_const_500_);
    return v___x_501_;
}
pub unsafe fn l_Lean_HeadIndex_const_elim(
    mut v_motive_502_: *mut crate::leanh::LeanObject,
    mut v_t_503_: *mut crate::leanh::LeanObject,
    mut v_h_504_: *mut crate::leanh::LeanObject,
    mut v_const_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_506_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_503_, v_const_505_);
    return v___x_506_;
}
pub unsafe fn l_Lean_HeadIndex_proj_elim___redArg(
    mut v_t_507_: *mut crate::leanh::LeanObject,
    mut v_proj_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_509_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_507_, v_proj_508_);
    return v___x_509_;
}
pub unsafe fn l_Lean_HeadIndex_proj_elim(
    mut v_motive_510_: *mut crate::leanh::LeanObject,
    mut v_t_511_: *mut crate::leanh::LeanObject,
    mut v_h_512_: *mut crate::leanh::LeanObject,
    mut v_proj_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_511_, v_proj_513_);
    return v___x_514_;
}
pub unsafe fn l_Lean_HeadIndex_lit_elim___redArg(
    mut v_t_515_: *mut crate::leanh::LeanObject,
    mut v_lit_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_515_, v_lit_516_);
    return v___x_517_;
}
pub unsafe fn l_Lean_HeadIndex_lit_elim(
    mut v_motive_518_: *mut crate::leanh::LeanObject,
    mut v_t_519_: *mut crate::leanh::LeanObject,
    mut v_h_520_: *mut crate::leanh::LeanObject,
    mut v_lit_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_519_, v_lit_521_);
    return v___x_522_;
}
pub unsafe fn l_Lean_HeadIndex_sort_elim___redArg(
    mut v_t_523_: *mut crate::leanh::LeanObject,
    mut v_sort_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_523_, v_sort_524_);
    return v___x_525_;
}
pub unsafe fn l_Lean_HeadIndex_sort_elim(
    mut v_motive_526_: *mut crate::leanh::LeanObject,
    mut v_t_527_: *mut crate::leanh::LeanObject,
    mut v_h_528_: *mut crate::leanh::LeanObject,
    mut v_sort_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_527_, v_sort_529_);
    return v___x_530_;
}
pub unsafe fn l_Lean_HeadIndex_lam_elim___redArg(
    mut v_t_531_: *mut crate::leanh::LeanObject,
    mut v_lam_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_531_, v_lam_532_);
    return v___x_533_;
}
pub unsafe fn l_Lean_HeadIndex_lam_elim(
    mut v_motive_534_: *mut crate::leanh::LeanObject,
    mut v_t_535_: *mut crate::leanh::LeanObject,
    mut v_h_536_: *mut crate::leanh::LeanObject,
    mut v_lam_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_535_, v_lam_537_);
    return v___x_538_;
}
pub unsafe fn l_Lean_HeadIndex_forallE_elim___redArg(
    mut v_t_539_: *mut crate::leanh::LeanObject,
    mut v_forallE_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_539_, v_forallE_540_);
    return v___x_541_;
}
pub unsafe fn l_Lean_HeadIndex_forallE_elim(
    mut v_motive_542_: *mut crate::leanh::LeanObject,
    mut v_t_543_: *mut crate::leanh::LeanObject,
    mut v_h_544_: *mut crate::leanh::LeanObject,
    mut v_forallE_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Lean_HeadIndex_ctorElim___redArg(v_t_543_, v_forallE_545_);
    return v___x_546_;
}
pub unsafe fn l_Lean_instBEqHeadIndex_beq(
    mut v_x_551_: *mut crate::leanh::LeanObject,
    mut v_x_552_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_551_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_552_) == 0 {
                let mut v_fvarId_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_fvarId_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_555_: u8 = 0;
                v_fvarId_553_ = crate::leanh::lean_ctor_get(v_x_551_, 0);
                v_fvarId_554_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
                v___x_555_ = l_Lean_instBEqFVarId_beq(v_fvarId_553_, v_fvarId_554_);
                return v___x_555_;
            } else {
                let mut v___x_556_: u8 = 0;
                v___x_556_ = 0;
                return v___x_556_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_552_) == 1 {
                let mut v_mvarId_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_mvarId_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_559_: u8 = 0;
                v_mvarId_557_ = crate::leanh::lean_ctor_get(v_x_551_, 0);
                v_mvarId_558_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
                v___x_559_ = l_Lean_instBEqMVarId_beq(v_mvarId_557_, v_mvarId_558_);
                return v___x_559_;
            } else {
                let mut v___x_560_: u8 = 0;
                v___x_560_ = 0;
                return v___x_560_;
            }
        }
        2 => {
            if crate::leanh::lean_obj_tag(v_x_552_) == 2 {
                let mut v_constName_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_constName_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_563_: u8 = 0;
                v_constName_561_ = crate::leanh::lean_ctor_get(v_x_551_, 0);
                v_constName_562_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
                v___x_563_ = lean_name_eq(v_constName_561_, v_constName_562_);
                return v___x_563_;
            } else {
                let mut v___x_564_: u8 = 0;
                v___x_564_ = 0;
                return v___x_564_;
            }
        }
        3 => {
            if crate::leanh::lean_obj_tag(v_x_552_) == 3 {
                let mut v_structName_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_idx_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_structName_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_idx_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_569_: u8 = 0;
                v_structName_565_ = crate::leanh::lean_ctor_get(v_x_551_, 0);
                v_idx_566_ = crate::leanh::lean_ctor_get(v_x_551_, 1);
                v_structName_567_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
                v_idx_568_ = crate::leanh::lean_ctor_get(v_x_552_, 1);
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
            if crate::leanh::lean_obj_tag(v_x_552_) == 4 {
                let mut v_litVal_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_litVal_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_574_: u8 = 0;
                v_litVal_572_ = crate::leanh::lean_ctor_get(v_x_551_, 0);
                v_litVal_573_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
                v___x_574_ = l_Lean_instBEqLiteral_beq(v_litVal_572_, v_litVal_573_);
                return v___x_574_;
            } else {
                let mut v___x_575_: u8 = 0;
                v___x_575_ = 0;
                return v___x_575_;
            }
        }
        5 => {
            if crate::leanh::lean_obj_tag(v_x_552_) == 5 {
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
            if crate::leanh::lean_obj_tag(v_x_552_) == 6 {
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
            if crate::leanh::lean_obj_tag(v_x_552_) == 7 {
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
    mut v_x_582_: *mut crate::leanh::LeanObject,
    mut v_x_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_584_: u8 = 0;
    let mut v_r_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_instBEqHeadIndex_beq(v_x_582_, v_x_583_);
    crate::leanh::lean_dec(v_x_583_);
    crate::leanh::lean_dec(v_x_582_);
    v_r_585_ = crate::leanh::lean_box((v_res_584_) as usize);
    return v_r_585_;
}
pub unsafe fn _init_l_Lean_instReprHeadIndex_repr___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_604_ = lean_nat_to_int(v___x_603_);
    return v___x_604_;
}
pub unsafe fn _init_l_Lean_instReprHeadIndex_repr___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_605_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_606_ = lean_nat_to_int(v___x_605_);
    return v___x_606_;
}
pub unsafe fn l_Lean_instReprHeadIndex_repr(
    mut v_x_631_: *mut crate::leanh::LeanObject,
    mut v_prec_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: u8 = 0;
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_constName_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: u8 = 0;
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___y_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_litVal_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_631_) {
                0 => {
                    v_fvarId_654_ = crate::leanh::lean_ctor_get(v_x_631_, 0);
                    crate::leanh::lean_inc(v_fvarId_654_);
                    crate::leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_665_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_666_ = lean_nat_dec_le(v___x_665_, v_prec_632_);
                    if v___x_666_ == 0 {
                        v___x_667_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_656_ = v___x_667_;
                        state = 4;
                        continue;
                    } else {
                        v___x_668_ = crate::leanh::lean_obj_once(
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
                    v_mvarId_669_ = crate::leanh::lean_ctor_get(v_x_631_, 0);
                    crate::leanh::lean_inc(v_mvarId_669_);
                    crate::leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_680_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_681_ = lean_nat_dec_le(v___x_680_, v_prec_632_);
                    if v___x_681_ == 0 {
                        v___x_682_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_671_ = v___x_682_;
                        state = 5;
                        continue;
                    } else {
                        v___x_683_ = crate::leanh::lean_obj_once(
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
                    v_constName_684_ = crate::leanh::lean_ctor_get(v_x_631_, 0);
                    crate::leanh::lean_inc(v_constName_684_);
                    crate::leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_695_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_696_ = lean_nat_dec_le(v___x_695_, v_prec_632_);
                    if v___x_696_ == 0 {
                        v___x_697_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_686_ = v___x_697_;
                        state = 6;
                        continue;
                    } else {
                        v___x_698_ = crate::leanh::lean_obj_once(
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
                    v_structName_699_ = crate::leanh::lean_ctor_get(v_x_631_, 0);
                    v_idx_700_ = crate::leanh::lean_ctor_get(v_x_631_, 1);
                    v_isSharedCheck_725_ = (!crate::leanh::lean_is_exclusive(v_x_631_)) as u8;
                    if v_isSharedCheck_725_ == 0 {
                        v___x_702_ = v_x_631_;
                        v_isShared_703_ = v_isSharedCheck_725_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_idx_700_);
                        crate::leanh::lean_inc(v_structName_699_);
                        crate::leanh::lean_dec(v_x_631_);
                        v___x_702_ = crate::leanh::lean_box(0);
                        v_isShared_703_ = v_isSharedCheck_725_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_litVal_726_ = crate::leanh::lean_ctor_get(v_x_631_, 0);
                    crate::leanh::lean_inc_ref(v_litVal_726_);
                    crate::leanh::lean_dec_ref_known(v_x_631_, 1);
                    v___x_737_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_738_ = lean_nat_dec_le(v___x_737_, v_prec_632_);
                    if v___x_738_ == 0 {
                        v___x_739_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_728_ = v___x_739_;
                        state = 10;
                        continue;
                    } else {
                        v___x_740_ = crate::leanh::lean_obj_once(
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
                    v___x_741_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_742_ = lean_nat_dec_le(v___x_741_, v_prec_632_);
                    if v___x_742_ == 0 {
                        v___x_743_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_634_ = v___x_743_;
                        state = 1;
                        continue;
                    } else {
                        v___x_744_ = crate::leanh::lean_obj_once(
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
                    v___x_745_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_746_ = lean_nat_dec_le(v___x_745_, v_prec_632_);
                    if v___x_746_ == 0 {
                        v___x_747_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_641_ = v___x_747_;
                        state = 2;
                        continue;
                    } else {
                        v___x_748_ = crate::leanh::lean_obj_once(
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
                    v___x_749_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_750_ = lean_nat_dec_le(v___x_749_, v_prec_632_);
                    if v___x_750_ == 0 {
                        v___x_751_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                            _init_l_Lean_instReprHeadIndex_repr___closed__9,
                        );
                        v___y_648_ = v___x_751_;
                        state = 3;
                        continue;
                    } else {
                        v___x_752_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_inc(v___y_634_);
                v___x_636_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_636_, 0, v___y_634_);
                crate::leanh::lean_ctor_set(v___x_636_, 1, v___x_635_);
                v___x_637_ = 0;
                v___x_638_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_638_, 0, v___x_636_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_638_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_637_,
                );
                v___x_639_ = l_Repr_addAppParen(v___x_638_, v_prec_632_);
                return v___x_639_;
            }
            2 => {
                v___x_642_ = l_Lean_instReprHeadIndex_repr___closed__3;
                crate::leanh::lean_inc(v___y_641_);
                v___x_643_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_643_, 0, v___y_641_);
                crate::leanh::lean_ctor_set(v___x_643_, 1, v___x_642_);
                v___x_644_ = 0;
                v___x_645_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_645_, 0, v___x_643_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_644_,
                );
                v___x_646_ = l_Repr_addAppParen(v___x_645_, v_prec_632_);
                return v___x_646_;
            }
            3 => {
                v___x_649_ = l_Lean_instReprHeadIndex_repr___closed__5;
                crate::leanh::lean_inc(v___y_648_);
                v___x_650_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_650_, 0, v___y_648_);
                crate::leanh::lean_ctor_set(v___x_650_, 1, v___x_649_);
                v___x_651_ = 0;
                v___x_652_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_652_, 0, v___x_650_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_652_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                v___x_653_ = l_Repr_addAppParen(v___x_652_, v_prec_632_);
                return v___x_653_;
            }
            4 => {
                v___x_657_ = l_Lean_instReprHeadIndex_repr___closed__8;
                v___x_658_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_659_ = l_Lean_Name_reprPrec(v_fvarId_654_, v___x_658_);
                v___x_660_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_660_, 0, v___x_657_);
                crate::leanh::lean_ctor_set(v___x_660_, 1, v___x_659_);
                crate::leanh::lean_inc(v___y_656_);
                v___x_661_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_661_, 0, v___y_656_);
                crate::leanh::lean_ctor_set(v___x_661_, 1, v___x_660_);
                v___x_662_ = 0;
                v___x_663_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_663_, 0, v___x_661_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_663_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_662_,
                );
                v___x_664_ = l_Repr_addAppParen(v___x_663_, v_prec_632_);
                return v___x_664_;
            }
            5 => {
                v___x_672_ = l_Lean_instReprHeadIndex_repr___closed__13;
                v___x_673_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_674_ = l_Lean_Name_reprPrec(v_mvarId_669_, v___x_673_);
                v___x_675_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_675_, 0, v___x_672_);
                crate::leanh::lean_ctor_set(v___x_675_, 1, v___x_674_);
                crate::leanh::lean_inc(v___y_671_);
                v___x_676_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_676_, 0, v___y_671_);
                crate::leanh::lean_ctor_set(v___x_676_, 1, v___x_675_);
                v___x_677_ = 0;
                v___x_678_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_678_, 0, v___x_676_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_678_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_677_,
                );
                v___x_679_ = l_Repr_addAppParen(v___x_678_, v_prec_632_);
                return v___x_679_;
            }
            6 => {
                v___x_687_ = l_Lean_instReprHeadIndex_repr___closed__16;
                v___x_688_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_689_ = l_Lean_Name_reprPrec(v_constName_684_, v___x_688_);
                v___x_690_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_687_);
                crate::leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
                crate::leanh::lean_inc(v___y_686_);
                v___x_691_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_691_, 0, v___y_686_);
                crate::leanh::lean_ctor_set(v___x_691_, 1, v___x_690_);
                v___x_692_ = 0;
                v___x_693_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_693_, 0, v___x_691_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_693_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_692_,
                );
                v___x_694_ = l_Repr_addAppParen(v___x_693_, v_prec_632_);
                return v___x_694_;
            }
            7 => {
                v___x_721_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_722_ = lean_nat_dec_le(v___x_721_, v_prec_632_);
                if v___x_722_ == 0 {
                    v___x_723_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_instReprHeadIndex_repr___closed__9_once),
                        _init_l_Lean_instReprHeadIndex_repr___closed__9,
                    );
                    v___y_705_ = v___x_723_;
                    state = 8;
                    continue;
                } else {
                    v___x_724_ = crate::leanh::lean_obj_once(
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
                v___x_706_ = crate::leanh::lean_box(1);
                v___x_707_ = l_Lean_instReprHeadIndex_repr___closed__19;
                v___x_708_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_709_ = l_Lean_Name_reprPrec(v_structName_699_, v___x_708_);
                if v_isShared_703_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_702_, 5);
                    crate::leanh::lean_ctor_set(v___x_702_, 1, v___x_709_);
                    crate::leanh::lean_ctor_set(v___x_702_, 0, v___x_707_);
                    v___x_711_ = v___x_702_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_720_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_709_);
                    v___x_711_ = v_reuseFailAlloc_720_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_712_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_712_, 0, v___x_711_);
                crate::leanh::lean_ctor_set(v___x_712_, 1, v___x_706_);
                v___x_713_ = l_Nat_reprFast(v_idx_700_);
                v___x_714_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_714_, 0, v___x_713_);
                v___x_715_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_712_);
                crate::leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
                crate::leanh::lean_inc(v___y_705_);
                v___x_716_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_716_, 0, v___y_705_);
                crate::leanh::lean_ctor_set(v___x_716_, 1, v___x_715_);
                v___x_717_ = 0;
                v___x_718_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_718_, 0, v___x_716_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_718_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_717_,
                );
                v___x_719_ = l_Repr_addAppParen(v___x_718_, v_prec_632_);
                return v___x_719_;
            }
            10 => {
                v___x_729_ = l_Lean_instReprHeadIndex_repr___closed__22;
                v___x_730_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_731_ = l_Lean_instReprLiteral_repr(v_litVal_726_, v___x_730_);
                v___x_732_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_729_);
                crate::leanh::lean_ctor_set(v___x_732_, 1, v___x_731_);
                crate::leanh::lean_inc(v___y_728_);
                v___x_733_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_733_, 0, v___y_728_);
                crate::leanh::lean_ctor_set(v___x_733_, 1, v___x_732_);
                v___x_734_ = 0;
                v___x_735_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_735_, 0, v___x_733_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_735_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_753_: *mut crate::leanh::LeanObject,
    mut v_prec_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_755_ = l_Lean_instReprHeadIndex_repr(v_x_753_, v_prec_754_);
    crate::leanh::lean_dec(v_prec_754_);
    return v_res_755_;
}
pub unsafe fn _init_l_Lean_HeadIndex_hash___closed__0() -> u64 {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u64 = 0;
    v___x_758_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_759_ = lean_uint64_of_nat(v___x_758_);
    return v___x_759_;
}
pub unsafe fn _init_l_Lean_HeadIndex_hash___closed__1() -> u64 {
    let mut v___x_760_: u64 = 0;
    let mut v___x_761_: u64 = 0;
    let mut v___x_762_: u64 = 0;
    v___x_760_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0_once),
        _init_l_Lean_HeadIndex_hash___closed__0,
    );
    v___x_761_ = 17u64;
    v___x_762_ = lean_uint64_mix_hash(v___x_761_, v___x_760_);
    return v___x_762_;
}
pub unsafe fn l_Lean_HeadIndex_hash(mut v_x_763_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v_fvarId_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u64 = 0;
    let mut v___x_766_: u64 = 0;
    let mut v___x_767_: u64 = 0;
    let mut v_mvarId_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: u64 = 0;
    let mut v___x_770_: u64 = 0;
    let mut v___x_771_: u64 = 0;
    let mut v_constName_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: u64 = 0;
    let mut v___x_774_: u64 = 0;
    let mut v_hash_775_: u64 = 0;
    let mut v___x_776_: u64 = 0;
    let mut v_structName_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u64 = 0;
    let mut v___y_781_: u64 = 0;
    let mut v___x_782_: u64 = 0;
    let mut v___x_783_: u64 = 0;
    let mut v___x_784_: u64 = 0;
    let mut v___x_785_: u64 = 0;
    let mut v_hash_786_: u64 = 0;
    let mut v_litVal_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: u64 = 0;
    let mut v___x_789_: u64 = 0;
    let mut v___x_790_: u64 = 0;
    let mut v___x_791_: u64 = 0;
    let mut v___x_792_: u64 = 0;
    let mut v___x_793_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_763_) {
                0 => {
                    v_fvarId_764_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                    v___x_765_ = 11u64;
                    v___x_766_ = l_Lean_instHashableFVarId_hash(v_fvarId_764_);
                    v___x_767_ = lean_uint64_mix_hash(v___x_765_, v___x_766_);
                    return v___x_767_;
                }
                1 => {
                    v_mvarId_768_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                    v___x_769_ = 13u64;
                    v___x_770_ = l_Lean_instHashableMVarId_hash(v_mvarId_768_);
                    v___x_771_ = lean_uint64_mix_hash(v___x_769_, v___x_770_);
                    return v___x_771_;
                }
                2 => {
                    v_constName_772_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                    v___x_773_ = 17u64;
                    if crate::leanh::lean_obj_tag(v_constName_772_) == 0 {
                        v___x_774_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__1_once),
                            _init_l_Lean_HeadIndex_hash___closed__1,
                        );
                        return v___x_774_;
                    } else {
                        v_hash_775_ = crate::leanh::lean_ctor_get_uint64(
                            v_constName_772_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_776_ = lean_uint64_mix_hash(v___x_773_, v_hash_775_);
                        return v___x_776_;
                    }
                }
                3 => {
                    v_structName_777_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                    v_idx_778_ = crate::leanh::lean_ctor_get(v_x_763_, 1);
                    v___x_779_ = 19u64;
                    if crate::leanh::lean_obj_tag(v_structName_777_) == 0 {
                        v___x_785_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_HeadIndex_hash___closed__0_once),
                            _init_l_Lean_HeadIndex_hash___closed__0,
                        );
                        v___y_781_ = v___x_785_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_786_ = crate::leanh::lean_ctor_get_uint64(
                            v_structName_777_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_781_ = v_hash_786_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v_litVal_787_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
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
    mut v_x_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_795_: u64 = 0;
    let mut v_r_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_HeadIndex_hash(v_x_794_);
    crate::leanh::lean_dec(v_x_794_);
    v_r_796_ = crate::leanh::lean_box_uint64(v_res_795_);
    return v_r_796_;
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(
    mut v_a_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_799_) {
                5 => {
                    v_fn_801_ = crate::leanh::lean_ctor_get(v_a_799_, 0);
                    v___x_802_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_803_ = lean_nat_add(v_a_800_, v___x_802_);
                    crate::leanh::lean_dec(v_a_800_);
                    v_a_799_ = v_fn_801_;
                    v_a_800_ = v___x_803_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_body_805_ = crate::leanh::lean_ctor_get(v_a_799_, 3);
                    v_a_799_ = v_body_805_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_807_ = crate::leanh::lean_ctor_get(v_a_799_, 1);
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
    mut v_a_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_a_809_, v_a_810_);
    crate::leanh::lean_dec_ref(v_a_809_);
    return v_res_811_;
}
pub unsafe fn l_Lean_Expr_headNumArgs(
    mut v_e_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_814_ = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgs_go(v_e_812_, v___x_813_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Expr_headNumArgs___boxed(
    mut v_e_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Expr_headNumArgs(v_e_815_);
    crate::leanh::lean_dec_ref(v_e_815_);
    return v_res_816_;
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(
    mut v_x_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_x_823_) {
                    2 => {
                        v_mvarId_824_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        crate::leanh::lean_inc(v_mvarId_824_);
                        v___x_825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_825_, 0, v_mvarId_824_);
                        v___x_826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_826_, 0, v___x_825_);
                        return v___x_826_;
                    }
                    1 => {
                        v_fvarId_827_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        crate::leanh::lean_inc(v_fvarId_827_);
                        v___x_828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_828_, 0, v_fvarId_827_);
                        v___x_829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_829_, 0, v___x_828_);
                        return v___x_829_;
                    }
                    4 => {
                        v_declName_830_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        crate::leanh::lean_inc(v_declName_830_);
                        v___x_831_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_831_, 0, v_declName_830_);
                        v___x_832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_832_, 0, v___x_831_);
                        return v___x_832_;
                    }
                    11 => {
                        v_typeName_833_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        v_idx_834_ = crate::leanh::lean_ctor_get(v_x_823_, 1);
                        crate::leanh::lean_inc(v_idx_834_);
                        crate::leanh::lean_inc(v_typeName_833_);
                        v___x_835_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_835_, 0, v_typeName_833_);
                        crate::leanh::lean_ctor_set(v___x_835_, 1, v_idx_834_);
                        v___x_836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_836_, 0, v___x_835_);
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
                        v_a_840_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        crate::leanh::lean_inc_ref(v_a_840_);
                        v___x_841_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_841_, 0, v_a_840_);
                        v___x_842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_842_, 0, v___x_841_);
                        return v___x_842_;
                    }
                    5 => {
                        v_fn_843_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        v_x_823_ = v_fn_843_;
                        state = 0;
                        continue;
                    }
                    8 => {
                        v_body_845_ = crate::leanh::lean_ctor_get(v_x_823_, 3);
                        v_x_823_ = v_body_845_;
                        state = 0;
                        continue;
                    }
                    10 => {
                        v_expr_847_ = crate::leanh::lean_ctor_get(v_x_823_, 1);
                        v_x_823_ = v_expr_847_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        v___x_849_ = crate::leanh::lean_box(0);
                        return v___x_849_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(
    mut v_x_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_851_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_x_850_);
    crate::leanh::lean_dec_ref(v_x_850_);
    return v_res_851_;
}
pub unsafe fn l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(
    mut v_msg_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = l_Lean_instInhabitedHeadIndex_default;
    v___x_854_ = lean_panic_fn_borrowed(v___x_853_, v_msg_852_);
    return v___x_854_;
}
pub unsafe fn _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2;
    v___x_859_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_860_ = crate::leanh::lean_unsigned_to_nat(104);
    v___x_861_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1;
    v___x_862_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__0;
    v___x_863_ =
        l_mkPanicMessageWithDecl(v___x_862_, v___x_861_, v___x_860_, v___x_859_, v___x_858_);
    return v___x_863_;
}
pub unsafe fn l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(
    mut v_x_864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_864_) {
                2 => {
                    v_mvarId_865_ = crate::leanh::lean_ctor_get(v_x_864_, 0);
                    crate::leanh::lean_inc(v_mvarId_865_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_866_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_866_, 0, v_mvarId_865_);
                    return v___x_866_;
                }
                1 => {
                    v_fvarId_867_ = crate::leanh::lean_ctor_get(v_x_864_, 0);
                    crate::leanh::lean_inc(v_fvarId_867_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_868_, 0, v_fvarId_867_);
                    return v___x_868_;
                }
                4 => {
                    v_declName_869_ = crate::leanh::lean_ctor_get(v_x_864_, 0);
                    crate::leanh::lean_inc(v_declName_869_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 2);
                    v___x_870_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_870_, 0, v_declName_869_);
                    return v___x_870_;
                }
                11 => {
                    v_typeName_871_ = crate::leanh::lean_ctor_get(v_x_864_, 0);
                    crate::leanh::lean_inc(v_typeName_871_);
                    v_idx_872_ = crate::leanh::lean_ctor_get(v_x_864_, 1);
                    crate::leanh::lean_inc(v_idx_872_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 3);
                    v___x_873_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_873_, 0, v_typeName_871_);
                    crate::leanh::lean_ctor_set(v___x_873_, 1, v_idx_872_);
                    return v___x_873_;
                }
                3 => {
                    crate::leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_874_ = crate::leanh::lean_box(5);
                    return v___x_874_;
                }
                6 => {
                    crate::leanh::lean_dec_ref_known(v_x_864_, 3);
                    v___x_875_ = crate::leanh::lean_box(6);
                    return v___x_875_;
                }
                7 => {
                    crate::leanh::lean_dec_ref_known(v_x_864_, 3);
                    v___x_876_ = crate::leanh::lean_box(7);
                    return v___x_876_;
                }
                9 => {
                    v_a_877_ = crate::leanh::lean_ctor_get(v_x_864_, 0);
                    crate::leanh::lean_inc_ref(v_a_877_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 1);
                    v___x_878_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_878_, 0, v_a_877_);
                    return v___x_878_;
                }
                5 => {
                    v_fn_879_ = crate::leanh::lean_ctor_get(v_x_864_, 0);
                    crate::leanh::lean_inc_ref(v_fn_879_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 2);
                    v_x_864_ = v_fn_879_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_value_881_ = crate::leanh::lean_ctor_get(v_x_864_, 2);
                    crate::leanh::lean_inc_ref(v_value_881_);
                    v_body_882_ = crate::leanh::lean_ctor_get(v_x_864_, 3);
                    crate::leanh::lean_inc_ref(v_body_882_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 4);
                    v___x_883_ = lean_expr_instantiate1(v_body_882_, v_value_881_);
                    crate::leanh::lean_dec_ref(v_value_881_);
                    crate::leanh::lean_dec_ref(v_body_882_);
                    v_x_864_ = v___x_883_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_885_ = crate::leanh::lean_ctor_get(v_x_864_, 1);
                    crate::leanh::lean_inc_ref(v_expr_885_);
                    crate::leanh::lean_dec_ref_known(v_x_864_, 2);
                    v_x_864_ = v_expr_885_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_864_);
                    v___x_887_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3), core::ptr::addr_of_mut!(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3_once), _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3);
                    v___x_888_ = l_panic___at___00__private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(v___x_887_);
                    return v___x_888_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_toHeadIndex(
    mut v_e_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(v_e_889_);
    if crate::leanh::lean_obj_tag(v___x_890_) == 0 {
        let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_891_ = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(v_e_889_);
        return v___x_891_;
    } else {
        let mut v_val_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_889_);
        v_val_892_ = crate::leanh::lean_ctor_get(v___x_890_, 0);
        crate::leanh::lean_inc(v_val_892_);
        crate::leanh::lean_dec_ref_known(v___x_890_, 1);
        return v_val_892_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_HeadIndex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_HeadIndex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_HeadIndex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_HeadIndex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_HeadIndex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_HeadIndex(builtin);
}
