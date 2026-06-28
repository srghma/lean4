// Lean compiler output
// Module: Lean.Data.DeclarationRange
// Imports: Lean.Data.Position
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::Position::{
    initialize_Lean_Data_Position, l_Lean_instDecidableEqPosition_decEq,
    l_Lean_instInhabitedPosition_default, l_Lean_instReprPosition_repr___redArg,
    runtime_initialize_Lean_Data_Position,
};
use crate::r#gen::Lean::Expr::{l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Lean_instInhabitedDeclarationRange_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedDeclarationRange_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRange_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRange: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value: LeanStringObject<3> =
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
        m_data: [123, 32, 0],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [112, 111, 115, 0],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [99, 104, 97, 114, 85, 116, 102, 49, 54, 0],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [101, 110, 100, 80, 111, 115, 0],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [101, 110, 100, 67, 104, 97, 114, 85, 116, 102, 49, 54, 0],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value: LeanStringObject<3> =
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
        m_data: [32, 125, 0],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__22_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange_repr___redArg___closed__23_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRange_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRange___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instReprDeclarationRange_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprDeclarationRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprDeclarationRange: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRange___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__1_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 82, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__2_value: LeanStringObject<3> =
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
        m_data: [109, 107, 0],
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
        as *mut LeanObject;
static l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__1_value)
                as *mut LeanObject,
            9209224823825377344 as *mut LeanObject,
        ],
    };
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
                as *mut LeanObject,
            3831656119348534840 as *mut LeanObject,
        ],
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__5_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [80, 111, 115, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__5_value)
        as *mut LeanObject;
static l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__5_value)
                as *mut LeanObject,
            7283224396379583297 as *mut LeanObject,
        ],
    };
pub static l_Lean_instToExprDeclarationRange___lam__0___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
                as *mut LeanObject,
            11125062533858197709 as *mut LeanObject,
        ],
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRange___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprDeclarationRange___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instToExprDeclarationRange___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprDeclarationRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___closed__0_value) as *mut LeanObject;
static l_Lean_instToExprDeclarationRange___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_instToExprDeclarationRange___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__1_value)
                as *mut LeanObject,
            9209224823825377344 as *mut LeanObject,
        ],
    };
static mut l_Lean_instToExprDeclarationRange___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___closed__1_value) as *mut LeanObject;
static mut l_Lean_instToExprDeclarationRange___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instToExprDeclarationRange___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprDeclarationRange___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instToExprDeclarationRange___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprDeclarationRange: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedDeclarationRanges_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedDeclarationRanges_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRanges_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationRanges: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [114, 97, 110, 103, 101, 0],
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            115, 101, 108, 101, 99, 116, 105, 111, 110, 82, 97, 110, 103, 101, 0,
        ],
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationRanges_repr___redArg___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDeclarationRanges_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDeclarationRanges___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instReprDeclarationRanges_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprDeclarationRanges___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprDeclarationRanges: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationRanges___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 82, 97, 110, 103, 101, 115, 0,
        ],
    };
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value)
        as *mut LeanObject;
static l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value)
                as *mut LeanObject,
            4956747414454776495 as *mut LeanObject,
        ],
    };
pub static l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__2_value)
                as *mut LeanObject,
            15960823074304203395 as *mut LeanObject,
        ],
    };
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprDeclarationRanges___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprDeclarationRanges___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instToExprDeclarationRanges___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprDeclarationRanges___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___closed__0_value) as *mut LeanObject;
static l_Lean_instToExprDeclarationRanges___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRange___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_instToExprDeclarationRanges___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value)
                as *mut LeanObject,
            4956747414454776495 as *mut LeanObject,
        ],
    };
static mut l_Lean_instToExprDeclarationRanges___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprDeclarationRanges___closed__1_value) as *mut LeanObject;
static mut l_Lean_instToExprDeclarationRanges___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instToExprDeclarationRanges___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprDeclarationRanges___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instToExprDeclarationRanges___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprDeclarationRanges: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedDeclarationLocation_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedDeclarationLocation_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationLocation_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclarationLocation: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationLocation_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprDeclarationLocation_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instReprDeclarationLocation___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instReprDeclarationLocation_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprDeclarationLocation___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprDeclarationLocation: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDeclarationLocation___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRange_default___closed__0() -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = lean_unsigned_to_nat(0);
    v___x_423_ = l_Lean_instInhabitedPosition_default;
    v___x_424_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_424_, 0, v___x_423_);
    lean_ctor_set(v___x_424_, 1, v___x_422_);
    lean_ctor_set(v___x_424_, 2, v___x_423_);
    lean_ctor_set(v___x_424_, 3, v___x_422_);
    return v___x_424_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRange_default() -> *mut LeanObject {
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    v___x_425_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRange_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRange_default___closed__0_once),
        _init_l_Lean_instInhabitedDeclarationRange_default___closed__0,
    );
    return v___x_425_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRange() -> *mut LeanObject {
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    v___x_426_ = l_Lean_instInhabitedDeclarationRange_default;
    return v___x_426_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange_decEq(
    mut v_x_427_: *mut LeanObject,
    mut v_x_428_: *mut LeanObject,
) -> u8 {
    let mut v_pos_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: u8 = 0;
    v_pos_429_ = lean_ctor_get(v_x_427_, 0);
    v_charUtf16_430_ = lean_ctor_get(v_x_427_, 1);
    v_endPos_431_ = lean_ctor_get(v_x_427_, 2);
    v_endCharUtf16_432_ = lean_ctor_get(v_x_427_, 3);
    v_pos_433_ = lean_ctor_get(v_x_428_, 0);
    v_charUtf16_434_ = lean_ctor_get(v_x_428_, 1);
    v_endPos_435_ = lean_ctor_get(v_x_428_, 2);
    v_endCharUtf16_436_ = lean_ctor_get(v_x_428_, 3);
    v___x_437_ = l_Lean_instDecidableEqPosition_decEq(v_pos_429_, v_pos_433_);
    if v___x_437_ == 0 {
        return v___x_437_;
    } else {
        let mut v___x_438_: u8 = 0;
        v___x_438_ = lean_nat_dec_eq(v_charUtf16_430_, v_charUtf16_434_);
        if v___x_438_ == 0 {
            return v___x_438_;
        } else {
            let mut v___x_439_: u8 = 0;
            v___x_439_ = l_Lean_instDecidableEqPosition_decEq(v_endPos_431_, v_endPos_435_);
            if v___x_439_ == 0 {
                return v___x_439_;
            } else {
                let mut v___x_440_: u8 = 0;
                v___x_440_ = lean_nat_dec_eq(v_endCharUtf16_432_, v_endCharUtf16_436_);
                return v___x_440_;
            }
        }
    }
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange_decEq___boxed(
    mut v_x_441_: *mut LeanObject,
    mut v_x_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_443_: u8 = 0;
    let mut v_r_444_: *mut LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_x_441_, v_x_442_);
    lean_dec_ref(v_x_442_);
    lean_dec_ref(v_x_441_);
    v_r_444_ = lean_box((v_res_443_) as usize);
    return v_r_444_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange(
    mut v_x_445_: *mut LeanObject,
    mut v_x_446_: *mut LeanObject,
) -> u8 {
    let mut v___x_447_: u8 = 0;
    v___x_447_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_x_445_, v_x_446_);
    return v___x_447_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationRange___boxed(
    mut v_x_448_: *mut LeanObject,
    mut v_x_449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_450_: u8 = 0;
    let mut v_r_451_: *mut LeanObject = core::ptr::null_mut();
    v_res_450_ = l_Lean_instDecidableEqDeclarationRange(v_x_448_, v_x_449_);
    lean_dec_ref(v_x_449_);
    lean_dec_ref(v_x_448_);
    v_r_451_ = lean_box((v_res_450_) as usize);
    return v_r_451_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprDeclarationRange_repr_spec__0(
    mut v_a_452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    v___x_453_ = lean_nat_to_int(v_a_452_);
    return v___x_453_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = lean_unsigned_to_nat(7);
    v___x_468_ = lean_nat_to_int(v___x_467_);
    return v___x_468_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__12() -> *mut LeanObject
{
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = lean_unsigned_to_nat(13);
    v___x_476_ = lean_nat_to_int(v___x_475_);
    return v___x_476_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15() -> *mut LeanObject
{
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_480_ = lean_unsigned_to_nat(10);
    v___x_481_ = lean_nat_to_int(v___x_480_);
    return v___x_481_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__18() -> *mut LeanObject
{
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_485_ = lean_unsigned_to_nat(16);
    v___x_486_ = lean_nat_to_int(v___x_485_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__20() -> *mut LeanObject
{
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__0;
    v___x_489_ = lean_string_length(v___x_488_);
    return v___x_489_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21() -> *mut LeanObject
{
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    v___x_490_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__20_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__20,
    );
    v___x_491_ = lean_nat_to_int(v___x_490_);
    return v___x_491_;
}
pub unsafe fn l_Lean_instReprDeclarationRange_repr___redArg(
    mut v_x_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: u8 = 0;
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    v_pos_497_ = lean_ctor_get(v_x_496_, 0);
    lean_inc_ref(v_pos_497_);
    v_charUtf16_498_ = lean_ctor_get(v_x_496_, 1);
    lean_inc(v_charUtf16_498_);
    v_endPos_499_ = lean_ctor_get(v_x_496_, 2);
    lean_inc_ref(v_endPos_499_);
    v_endCharUtf16_500_ = lean_ctor_get(v_x_496_, 3);
    lean_inc(v_endCharUtf16_500_);
    lean_dec_ref(v_x_496_);
    v___x_501_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__5;
    v___x_502_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__6;
    v___x_503_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__7_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__7,
    );
    v___x_504_ = l_Lean_instReprPosition_repr___redArg(v_pos_497_);
    v___x_505_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_505_, 0, v___x_503_);
    lean_ctor_set(v___x_505_, 1, v___x_504_);
    v___x_506_ = 0;
    v___x_507_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_507_, 0, v___x_505_);
    lean_ctor_set_uint8(
        v___x_507_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_508_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_508_, 0, v___x_502_);
    lean_ctor_set(v___x_508_, 1, v___x_507_);
    v___x_509_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__9;
    v___x_510_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_510_, 0, v___x_508_);
    lean_ctor_set(v___x_510_, 1, v___x_509_);
    v___x_511_ = lean_box(1);
    v___x_512_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_512_, 0, v___x_510_);
    lean_ctor_set(v___x_512_, 1, v___x_511_);
    v___x_513_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__11;
    v___x_514_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_514_, 0, v___x_512_);
    lean_ctor_set(v___x_514_, 1, v___x_513_);
    v___x_515_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_515_, 0, v___x_514_);
    lean_ctor_set(v___x_515_, 1, v___x_501_);
    v___x_516_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__12_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__12,
    );
    v___x_517_ = l_Nat_reprFast(v_charUtf16_498_);
    v___x_518_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_518_, 0, v___x_517_);
    v___x_519_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_519_, 0, v___x_516_);
    lean_ctor_set(v___x_519_, 1, v___x_518_);
    v___x_520_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_520_, 0, v___x_519_);
    lean_ctor_set_uint8(
        v___x_520_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_521_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_521_, 0, v___x_515_);
    lean_ctor_set(v___x_521_, 1, v___x_520_);
    v___x_522_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_522_, 0, v___x_521_);
    lean_ctor_set(v___x_522_, 1, v___x_509_);
    v___x_523_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_523_, 0, v___x_522_);
    lean_ctor_set(v___x_523_, 1, v___x_511_);
    v___x_524_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__14;
    v___x_525_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_525_, 0, v___x_523_);
    lean_ctor_set(v___x_525_, 1, v___x_524_);
    v___x_526_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_526_, 0, v___x_525_);
    lean_ctor_set(v___x_526_, 1, v___x_501_);
    v___x_527_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15,
    );
    v___x_528_ = l_Lean_instReprPosition_repr___redArg(v_endPos_499_);
    v___x_529_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_529_, 0, v___x_527_);
    lean_ctor_set(v___x_529_, 1, v___x_528_);
    v___x_530_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_530_, 0, v___x_529_);
    lean_ctor_set_uint8(
        v___x_530_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_531_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_531_, 0, v___x_526_);
    lean_ctor_set(v___x_531_, 1, v___x_530_);
    v___x_532_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_532_, 0, v___x_531_);
    lean_ctor_set(v___x_532_, 1, v___x_509_);
    v___x_533_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_533_, 0, v___x_532_);
    lean_ctor_set(v___x_533_, 1, v___x_511_);
    v___x_534_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__17;
    v___x_535_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_535_, 0, v___x_533_);
    lean_ctor_set(v___x_535_, 1, v___x_534_);
    v___x_536_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_536_, 0, v___x_535_);
    lean_ctor_set(v___x_536_, 1, v___x_501_);
    v___x_537_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__18_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__18,
    );
    v___x_538_ = l_Nat_reprFast(v_endCharUtf16_500_);
    v___x_539_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_539_, 0, v___x_538_);
    v___x_540_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_540_, 0, v___x_537_);
    lean_ctor_set(v___x_540_, 1, v___x_539_);
    v___x_541_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_541_, 0, v___x_540_);
    lean_ctor_set_uint8(
        v___x_541_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_506_,
    );
    v___x_542_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_542_, 0, v___x_536_);
    lean_ctor_set(v___x_542_, 1, v___x_541_);
    v___x_543_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once),
        _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21,
    );
    v___x_544_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__22;
    v___x_545_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_545_, 0, v___x_544_);
    lean_ctor_set(v___x_545_, 1, v___x_542_);
    v___x_546_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__23;
    v___x_547_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_547_, 0, v___x_545_);
    lean_ctor_set(v___x_547_, 1, v___x_546_);
    v___x_548_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_548_, 0, v___x_543_);
    lean_ctor_set(v___x_548_, 1, v___x_547_);
    v___x_549_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_549_, 0, v___x_548_);
    lean_ctor_set_uint8(
        v___x_549_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_506_,
    );
    return v___x_549_;
}
pub unsafe fn l_Lean_instReprDeclarationRange_repr(
    mut v_x_550_: *mut LeanObject,
    mut v_prec_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    v___x_552_ = l_Lean_instReprDeclarationRange_repr___redArg(v_x_550_);
    return v___x_552_;
}
pub unsafe fn l_Lean_instReprDeclarationRange_repr___boxed(
    mut v_x_553_: *mut LeanObject,
    mut v_prec_554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_555_: *mut LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lean_instReprDeclarationRange_repr(v_x_553_, v_prec_554_);
    lean_dec(v_prec_554_);
    return v_res_555_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    v___x_565_ = lean_box(0);
    v___x_566_ = l_Lean_instToExprDeclarationRange___lam__0___closed__3;
    v___x_567_ = l_Lean_mkConst(v___x_566_, v___x_565_);
    return v___x_567_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7() -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ = lean_box(0);
    v___x_574_ = l_Lean_instToExprDeclarationRange___lam__0___closed__6;
    v___x_575_ = l_Lean_mkConst(v___x_574_, v___x_573_);
    return v___x_575_;
}
pub unsafe fn l_Lean_instToExprDeclarationRange___lam__0(
    mut v_r_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v_pos_577_ = lean_ctor_get(v_r_576_, 0);
    lean_inc_ref(v_pos_577_);
    v_endPos_578_ = lean_ctor_get(v_r_576_, 2);
    lean_inc_ref(v_endPos_578_);
    v_charUtf16_579_ = lean_ctor_get(v_r_576_, 1);
    lean_inc(v_charUtf16_579_);
    v_endCharUtf16_580_ = lean_ctor_get(v_r_576_, 3);
    lean_inc(v_endCharUtf16_580_);
    lean_dec_ref(v_r_576_);
    v_line_581_ = lean_ctor_get(v_pos_577_, 0);
    lean_inc(v_line_581_);
    v_column_582_ = lean_ctor_get(v_pos_577_, 1);
    lean_inc(v_column_582_);
    lean_dec_ref(v_pos_577_);
    v_line_583_ = lean_ctor_get(v_endPos_578_, 0);
    lean_inc(v_line_583_);
    v_column_584_ = lean_ctor_get(v_endPos_578_, 1);
    lean_inc(v_column_584_);
    lean_dec_ref(v_endPos_578_);
    v___x_585_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4,
    );
    v___x_586_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7,
    );
    v___x_587_ = l_Lean_mkNatLit(v_line_581_);
    v___x_588_ = l_Lean_mkNatLit(v_column_582_);
    v___x_589_ = lean_unsigned_to_nat(2);
    v___x_590_ = lean_mk_empty_array_with_capacity(v___x_589_);
    lean_inc_ref(v___x_590_);
    v___x_591_ = lean_array_push(v___x_590_, v___x_587_);
    v___x_592_ = lean_array_push(v___x_591_, v___x_588_);
    v___x_593_ = l_Lean_mkAppN(v___x_586_, v___x_592_);
    lean_dec_ref(v___x_592_);
    v___x_594_ = l_Lean_mkNatLit(v_charUtf16_579_);
    v___x_595_ = l_Lean_mkNatLit(v_line_583_);
    v___x_596_ = l_Lean_mkNatLit(v_column_584_);
    v___x_597_ = lean_array_push(v___x_590_, v___x_595_);
    v___x_598_ = lean_array_push(v___x_597_, v___x_596_);
    v___x_599_ = l_Lean_mkAppN(v___x_586_, v___x_598_);
    lean_dec_ref(v___x_598_);
    v___x_600_ = l_Lean_mkNatLit(v_endCharUtf16_580_);
    v___x_601_ = lean_unsigned_to_nat(4);
    v___x_602_ = lean_mk_empty_array_with_capacity(v___x_601_);
    v___x_603_ = lean_array_push(v___x_602_, v___x_593_);
    v___x_604_ = lean_array_push(v___x_603_, v___x_594_);
    v___x_605_ = lean_array_push(v___x_604_, v___x_599_);
    v___x_606_ = lean_array_push(v___x_605_, v___x_600_);
    v___x_607_ = l_Lean_mkAppN(v___x_585_, v___x_606_);
    lean_dec_ref(v___x_606_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___closed__2() -> *mut LeanObject {
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    v___x_612_ = lean_box(0);
    v___x_613_ = l_Lean_instToExprDeclarationRange___closed__1;
    v___x_614_ = l_Lean_mkConst(v___x_613_, v___x_612_);
    return v___x_614_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange___closed__3() -> *mut LeanObject {
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_615_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__2_once),
        _init_l_Lean_instToExprDeclarationRange___closed__2,
    );
    v___f_616_ = l_Lean_instToExprDeclarationRange___closed__0;
    v___x_617_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_617_, 0, v___f_616_);
    lean_ctor_set(v___x_617_, 1, v___x_615_);
    return v___x_617_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRange() -> *mut LeanObject {
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    v___x_618_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___closed__3_once),
        _init_l_Lean_instToExprDeclarationRange___closed__3,
    );
    return v___x_618_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRanges_default___closed__0() -> *mut LeanObject {
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    v___x_619_ = l_Lean_instInhabitedDeclarationRange_default;
    v___x_620_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_620_, 0, v___x_619_);
    lean_ctor_set(v___x_620_, 1, v___x_619_);
    return v___x_620_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRanges_default() -> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    v___x_621_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRanges_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationRanges_default___closed__0_once),
        _init_l_Lean_instInhabitedDeclarationRanges_default___closed__0,
    );
    return v___x_621_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationRanges() -> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = l_Lean_instInhabitedDeclarationRanges_default;
    return v___x_622_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4() -> *mut LeanObject
{
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    v___x_632_ = lean_unsigned_to_nat(9);
    v___x_633_ = lean_nat_to_int(v___x_632_);
    return v___x_633_;
}
pub unsafe fn _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__7() -> *mut LeanObject
{
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    v___x_637_ = lean_unsigned_to_nat(18);
    v___x_638_ = lean_nat_to_int(v___x_637_);
    return v___x_638_;
}
pub unsafe fn l_Lean_instReprDeclarationRanges_repr___redArg(
    mut v_x_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_range_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_644_: u8 = 0;
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_range_640_ = lean_ctor_get(v_x_639_, 0);
                v_selectionRange_641_ = lean_ctor_get(v_x_639_, 1);
                v_isSharedCheck_674_ = (!lean_is_exclusive(v_x_639_)) as u8;
                if v_isSharedCheck_674_ == 0 {
                    v___x_643_ = v_x_639_;
                    v_isShared_644_ = v_isSharedCheck_674_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_selectionRange_641_);
                    lean_inc(v_range_640_);
                    lean_dec(v_x_639_);
                    v___x_643_ = lean_box(0);
                    v_isShared_644_ = v_isSharedCheck_674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_645_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__5;
                v___x_646_ = l_Lean_instReprDeclarationRanges_repr___redArg___closed__3;
                v___x_647_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4,
                );
                v___x_648_ = l_Lean_instReprDeclarationRange_repr___redArg(v_range_640_);
                if v_isShared_644_ == 0 {
                    lean_ctor_set_tag(v___x_643_, 4);
                    lean_ctor_set(v___x_643_, 1, v___x_648_);
                    lean_ctor_set(v___x_643_, 0, v___x_647_);
                    v___x_650_ = v___x_643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_647_);
                    lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_648_);
                    v___x_650_ = v_reuseFailAlloc_673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_651_ = 0;
                v___x_652_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_652_, 0, v___x_650_);
                lean_ctor_set_uint8(
                    v___x_652_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                v___x_653_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_653_, 0, v___x_646_);
                lean_ctor_set(v___x_653_, 1, v___x_652_);
                v___x_654_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__9;
                v___x_655_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_655_, 0, v___x_653_);
                lean_ctor_set(v___x_655_, 1, v___x_654_);
                v___x_656_ = lean_box(1);
                v___x_657_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_657_, 0, v___x_655_);
                lean_ctor_set(v___x_657_, 1, v___x_656_);
                v___x_658_ = l_Lean_instReprDeclarationRanges_repr___redArg___closed__6;
                v___x_659_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_659_, 0, v___x_657_);
                lean_ctor_set(v___x_659_, 1, v___x_658_);
                v___x_660_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_660_, 0, v___x_659_);
                lean_ctor_set(v___x_660_, 1, v___x_645_);
                v___x_661_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__7_once
                    ),
                    _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__7,
                );
                v___x_662_ = l_Lean_instReprDeclarationRange_repr___redArg(v_selectionRange_641_);
                v___x_663_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_663_, 0, v___x_661_);
                lean_ctor_set(v___x_663_, 1, v___x_662_);
                v___x_664_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_664_, 0, v___x_663_);
                lean_ctor_set_uint8(
                    v___x_664_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                v___x_665_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_665_, 0, v___x_660_);
                lean_ctor_set(v___x_665_, 1, v___x_664_);
                v___x_666_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once
                    ),
                    _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21,
                );
                v___x_667_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__22;
                v___x_668_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_668_, 0, v___x_667_);
                lean_ctor_set(v___x_668_, 1, v___x_665_);
                v___x_669_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__23;
                v___x_670_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_670_, 0, v___x_668_);
                lean_ctor_set(v___x_670_, 1, v___x_669_);
                v___x_671_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_671_, 0, v___x_666_);
                lean_ctor_set(v___x_671_, 1, v___x_670_);
                v___x_672_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_672_, 0, v___x_671_);
                lean_ctor_set_uint8(
                    v___x_672_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_651_,
                );
                return v___x_672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprDeclarationRanges_repr(
    mut v_x_675_: *mut LeanObject,
    mut v_prec_676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    v___x_677_ = l_Lean_instReprDeclarationRanges_repr___redArg(v_x_675_);
    return v___x_677_;
}
pub unsafe fn l_Lean_instReprDeclarationRanges_repr___boxed(
    mut v_x_678_: *mut LeanObject,
    mut v_prec_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lean_instReprDeclarationRanges_repr(v_x_678_, v_prec_679_);
    lean_dec(v_prec_679_);
    return v_res_680_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_688_ = lean_box(0);
    v___x_689_ = l_Lean_instToExprDeclarationRanges___lam__0___closed__1;
    v___x_690_ = l_Lean_mkConst(v___x_689_, v___x_688_);
    return v___x_690_;
}
pub unsafe fn l_Lean_instToExprDeclarationRanges___lam__0(
    mut v_r_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_range_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v_range_692_ = lean_ctor_get(v_r_691_, 0);
    lean_inc_ref(v_range_692_);
    v_selectionRange_693_ = lean_ctor_get(v_r_691_, 1);
    lean_inc_ref(v_selectionRange_693_);
    lean_dec_ref(v_r_691_);
    v_pos_694_ = lean_ctor_get(v_range_692_, 0);
    lean_inc_ref(v_pos_694_);
    v_charUtf16_695_ = lean_ctor_get(v_range_692_, 1);
    lean_inc(v_charUtf16_695_);
    v_endPos_696_ = lean_ctor_get(v_range_692_, 2);
    lean_inc_ref(v_endPos_696_);
    v_endCharUtf16_697_ = lean_ctor_get(v_range_692_, 3);
    lean_inc(v_endCharUtf16_697_);
    lean_dec_ref(v_range_692_);
    v___x_698_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___lam__0___closed__2_once),
        _init_l_Lean_instToExprDeclarationRanges___lam__0___closed__2,
    );
    v_line_699_ = lean_ctor_get(v_pos_694_, 0);
    lean_inc(v_line_699_);
    v_column_700_ = lean_ctor_get(v_pos_694_, 1);
    lean_inc(v_column_700_);
    lean_dec_ref(v_pos_694_);
    v_line_701_ = lean_ctor_get(v_endPos_696_, 0);
    lean_inc(v_line_701_);
    v_column_702_ = lean_ctor_get(v_endPos_696_, 1);
    lean_inc(v_column_702_);
    lean_dec_ref(v_endPos_696_);
    v___x_703_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__4_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4,
    );
    v_pos_704_ = lean_ctor_get(v_selectionRange_693_, 0);
    lean_inc_ref(v_pos_704_);
    v_charUtf16_705_ = lean_ctor_get(v_selectionRange_693_, 1);
    lean_inc(v_charUtf16_705_);
    v_endPos_706_ = lean_ctor_get(v_selectionRange_693_, 2);
    lean_inc_ref(v_endPos_706_);
    v_endCharUtf16_707_ = lean_ctor_get(v_selectionRange_693_, 3);
    lean_inc(v_endCharUtf16_707_);
    lean_dec_ref(v_selectionRange_693_);
    v_line_708_ = lean_ctor_get(v_pos_704_, 0);
    lean_inc(v_line_708_);
    v_column_709_ = lean_ctor_get(v_pos_704_, 1);
    lean_inc(v_column_709_);
    lean_dec_ref(v_pos_704_);
    v___x_710_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRange___lam__0___closed__7_once),
        _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7,
    );
    v___x_711_ = l_Lean_mkNatLit(v_line_699_);
    v___x_712_ = l_Lean_mkNatLit(v_column_700_);
    v___x_713_ = lean_unsigned_to_nat(2);
    v___x_714_ = lean_mk_empty_array_with_capacity(v___x_713_);
    lean_inc_ref_n(v___x_714_, 4);
    v___x_715_ = lean_array_push(v___x_714_, v___x_711_);
    v___x_716_ = lean_array_push(v___x_715_, v___x_712_);
    v___x_717_ = l_Lean_mkAppN(v___x_710_, v___x_716_);
    lean_dec_ref(v___x_716_);
    v_line_718_ = lean_ctor_get(v_endPos_706_, 0);
    lean_inc(v_line_718_);
    v_column_719_ = lean_ctor_get(v_endPos_706_, 1);
    lean_inc(v_column_719_);
    lean_dec_ref(v_endPos_706_);
    v___x_720_ = l_Lean_mkNatLit(v_line_701_);
    v___x_721_ = l_Lean_mkNatLit(v_column_702_);
    v___x_722_ = lean_array_push(v___x_714_, v___x_720_);
    v___x_723_ = lean_array_push(v___x_722_, v___x_721_);
    v___x_724_ = l_Lean_mkAppN(v___x_710_, v___x_723_);
    lean_dec_ref(v___x_723_);
    v___x_725_ = l_Lean_mkNatLit(v_charUtf16_695_);
    v___x_726_ = l_Lean_mkNatLit(v_endCharUtf16_697_);
    v___x_727_ = lean_unsigned_to_nat(4);
    v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
    lean_inc_ref(v___x_728_);
    v___x_729_ = lean_array_push(v___x_728_, v___x_717_);
    v___x_730_ = lean_array_push(v___x_729_, v___x_725_);
    v___x_731_ = lean_array_push(v___x_730_, v___x_724_);
    v___x_732_ = lean_array_push(v___x_731_, v___x_726_);
    v___x_733_ = l_Lean_mkAppN(v___x_703_, v___x_732_);
    lean_dec_ref(v___x_732_);
    v___x_734_ = l_Lean_mkNatLit(v_line_708_);
    v___x_735_ = l_Lean_mkNatLit(v_column_709_);
    v___x_736_ = lean_array_push(v___x_714_, v___x_734_);
    v___x_737_ = lean_array_push(v___x_736_, v___x_735_);
    v___x_738_ = l_Lean_mkAppN(v___x_710_, v___x_737_);
    lean_dec_ref(v___x_737_);
    v___x_739_ = l_Lean_mkNatLit(v_charUtf16_705_);
    v___x_740_ = l_Lean_mkNatLit(v_line_718_);
    v___x_741_ = l_Lean_mkNatLit(v_column_719_);
    v___x_742_ = lean_array_push(v___x_714_, v___x_740_);
    v___x_743_ = lean_array_push(v___x_742_, v___x_741_);
    v___x_744_ = l_Lean_mkAppN(v___x_710_, v___x_743_);
    lean_dec_ref(v___x_743_);
    v___x_745_ = l_Lean_mkNatLit(v_endCharUtf16_707_);
    v___x_746_ = lean_array_push(v___x_728_, v___x_738_);
    v___x_747_ = lean_array_push(v___x_746_, v___x_739_);
    v___x_748_ = lean_array_push(v___x_747_, v___x_744_);
    v___x_749_ = lean_array_push(v___x_748_, v___x_745_);
    v___x_750_ = l_Lean_mkAppN(v___x_703_, v___x_749_);
    lean_dec_ref(v___x_749_);
    v___x_751_ = lean_array_push(v___x_714_, v___x_733_);
    v___x_752_ = lean_array_push(v___x_751_, v___x_750_);
    v___x_753_ = l_Lean_mkAppN(v___x_698_, v___x_752_);
    lean_dec_ref(v___x_752_);
    return v___x_753_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges___closed__2() -> *mut LeanObject {
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_758_ = lean_box(0);
    v___x_759_ = l_Lean_instToExprDeclarationRanges___closed__1;
    v___x_760_ = l_Lean_mkConst(v___x_759_, v___x_758_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges___closed__3() -> *mut LeanObject {
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v___x_761_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__2_once),
        _init_l_Lean_instToExprDeclarationRanges___closed__2,
    );
    v___f_762_ = l_Lean_instToExprDeclarationRanges___closed__0;
    v___x_763_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_763_, 0, v___f_762_);
    lean_ctor_set(v___x_763_, 1, v___x_761_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lean_instToExprDeclarationRanges() -> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprDeclarationRanges___closed__3_once),
        _init_l_Lean_instToExprDeclarationRanges___closed__3,
    );
    return v___x_764_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationLocation_default___closed__0() -> *mut LeanObject
{
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = l_Lean_instInhabitedDeclarationRange_default;
    v___x_766_ = lean_box(0);
    v___x_767_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_767_, 0, v___x_766_);
    lean_ctor_set(v___x_767_, 1, v___x_765_);
    return v___x_767_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationLocation_default() -> *mut LeanObject {
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    v___x_768_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationLocation_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclarationLocation_default___closed__0_once),
        _init_l_Lean_instInhabitedDeclarationLocation_default___closed__0,
    );
    return v___x_768_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclarationLocation() -> *mut LeanObject {
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    v___x_769_ = l_Lean_instInhabitedDeclarationLocation_default;
    return v___x_769_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation_decEq(
    mut v_x_770_: *mut LeanObject,
    mut v_x_771_: *mut LeanObject,
) -> u8 {
    let mut v_module_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    v_module_772_ = lean_ctor_get(v_x_770_, 0);
    v_range_773_ = lean_ctor_get(v_x_770_, 1);
    v_module_774_ = lean_ctor_get(v_x_771_, 0);
    v_range_775_ = lean_ctor_get(v_x_771_, 1);
    v___x_776_ = lean_name_eq(v_module_772_, v_module_774_);
    if v___x_776_ == 0 {
        return v___x_776_;
    } else {
        let mut v___x_777_: u8 = 0;
        v___x_777_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_range_773_, v_range_775_);
        return v___x_777_;
    }
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation_decEq___boxed(
    mut v_x_778_: *mut LeanObject,
    mut v_x_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_780_: u8 = 0;
    let mut v_r_781_: *mut LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Lean_instDecidableEqDeclarationLocation_decEq(v_x_778_, v_x_779_);
    lean_dec_ref(v_x_779_);
    lean_dec_ref(v_x_778_);
    v_r_781_ = lean_box((v_res_780_) as usize);
    return v_r_781_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation(
    mut v_x_782_: *mut LeanObject,
    mut v_x_783_: *mut LeanObject,
) -> u8 {
    let mut v___x_784_: u8 = 0;
    v___x_784_ = l_Lean_instDecidableEqDeclarationLocation_decEq(v_x_782_, v_x_783_);
    return v___x_784_;
}
pub unsafe fn l_Lean_instDecidableEqDeclarationLocation___boxed(
    mut v_x_785_: *mut LeanObject,
    mut v_x_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_787_: u8 = 0;
    let mut v_r_788_: *mut LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_instDecidableEqDeclarationLocation(v_x_785_, v_x_786_);
    lean_dec_ref(v_x_786_);
    lean_dec_ref(v_x_785_);
    v_r_788_ = lean_box((v_res_787_) as usize);
    return v_r_788_;
}
pub unsafe fn l_Lean_instReprDeclarationLocation_repr___redArg(
    mut v_x_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_module_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_803_: u8 = 0;
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_module_799_ = lean_ctor_get(v_x_798_, 0);
                v_range_800_ = lean_ctor_get(v_x_798_, 1);
                v_isSharedCheck_834_ = (!lean_is_exclusive(v_x_798_)) as u8;
                if v_isSharedCheck_834_ == 0 {
                    v___x_802_ = v_x_798_;
                    v_isShared_803_ = v_isSharedCheck_834_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_range_800_);
                    lean_inc(v_module_799_);
                    lean_dec(v_x_798_);
                    v___x_802_ = lean_box(0);
                    v_isShared_803_ = v_isSharedCheck_834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_804_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__5;
                v___x_805_ = l_Lean_instReprDeclarationLocation_repr___redArg___closed__3;
                v___x_806_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once
                    ),
                    _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15,
                );
                v___x_807_ = lean_unsigned_to_nat(0);
                v___x_808_ = l_Lean_Name_reprPrec(v_module_799_, v___x_807_);
                if v_isShared_803_ == 0 {
                    lean_ctor_set_tag(v___x_802_, 4);
                    lean_ctor_set(v___x_802_, 1, v___x_808_);
                    lean_ctor_set(v___x_802_, 0, v___x_806_);
                    v___x_810_ = v___x_802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_833_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_806_);
                    lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_808_);
                    v___x_810_ = v_reuseFailAlloc_833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_811_ = 0;
                v___x_812_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_812_, 0, v___x_810_);
                lean_ctor_set_uint8(
                    v___x_812_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                v___x_813_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_813_, 0, v___x_805_);
                lean_ctor_set(v___x_813_, 1, v___x_812_);
                v___x_814_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__9;
                v___x_815_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_815_, 0, v___x_813_);
                lean_ctor_set(v___x_815_, 1, v___x_814_);
                v___x_816_ = lean_box(1);
                v___x_817_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_817_, 0, v___x_815_);
                lean_ctor_set(v___x_817_, 1, v___x_816_);
                v___x_818_ = l_Lean_instReprDeclarationRanges_repr___redArg___closed__1;
                v___x_819_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_819_, 0, v___x_817_);
                lean_ctor_set(v___x_819_, 1, v___x_818_);
                v___x_820_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_820_, 0, v___x_819_);
                lean_ctor_set(v___x_820_, 1, v___x_804_);
                v___x_821_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once
                    ),
                    _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4,
                );
                v___x_822_ = l_Lean_instReprDeclarationRange_repr___redArg(v_range_800_);
                v___x_823_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_823_, 0, v___x_821_);
                lean_ctor_set(v___x_823_, 1, v___x_822_);
                v___x_824_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_824_, 0, v___x_823_);
                lean_ctor_set_uint8(
                    v___x_824_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                v___x_825_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_825_, 0, v___x_820_);
                lean_ctor_set(v___x_825_, 1, v___x_824_);
                v___x_826_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once
                    ),
                    _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21,
                );
                v___x_827_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__22;
                v___x_828_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_828_, 0, v___x_827_);
                lean_ctor_set(v___x_828_, 1, v___x_825_);
                v___x_829_ = l_Lean_instReprDeclarationRange_repr___redArg___closed__23;
                v___x_830_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_830_, 0, v___x_828_);
                lean_ctor_set(v___x_830_, 1, v___x_829_);
                v___x_831_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_831_, 0, v___x_826_);
                lean_ctor_set(v___x_831_, 1, v___x_830_);
                v___x_832_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_832_, 0, v___x_831_);
                lean_ctor_set_uint8(
                    v___x_832_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                return v___x_832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprDeclarationLocation_repr(
    mut v_x_835_: *mut LeanObject,
    mut v_prec_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_837_ = l_Lean_instReprDeclarationLocation_repr___redArg(v_x_835_);
    return v___x_837_;
}
pub unsafe fn l_Lean_instReprDeclarationLocation_repr___boxed(
    mut v_x_838_: *mut LeanObject,
    mut v_prec_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_840_: *mut LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Lean_instReprDeclarationLocation_repr(v_x_838_, v_prec_839_);
    lean_dec(v_prec_839_);
    return v_res_840_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Position(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedDeclarationRange_default =
        _init_l_Lean_instInhabitedDeclarationRange_default();
    lean_mark_persistent(l_Lean_instInhabitedDeclarationRange_default);
    l_Lean_instInhabitedDeclarationRange = _init_l_Lean_instInhabitedDeclarationRange();
    lean_mark_persistent(l_Lean_instInhabitedDeclarationRange);
    l_Lean_instToExprDeclarationRange = _init_l_Lean_instToExprDeclarationRange();
    lean_mark_persistent(l_Lean_instToExprDeclarationRange);
    l_Lean_instInhabitedDeclarationRanges_default =
        _init_l_Lean_instInhabitedDeclarationRanges_default();
    lean_mark_persistent(l_Lean_instInhabitedDeclarationRanges_default);
    l_Lean_instInhabitedDeclarationRanges = _init_l_Lean_instInhabitedDeclarationRanges();
    lean_mark_persistent(l_Lean_instInhabitedDeclarationRanges);
    l_Lean_instToExprDeclarationRanges = _init_l_Lean_instToExprDeclarationRanges();
    lean_mark_persistent(l_Lean_instToExprDeclarationRanges);
    l_Lean_instInhabitedDeclarationLocation_default =
        _init_l_Lean_instInhabitedDeclarationLocation_default();
    lean_mark_persistent(l_Lean_instInhabitedDeclarationLocation_default);
    l_Lean_instInhabitedDeclarationLocation = _init_l_Lean_instInhabitedDeclarationLocation();
    lean_mark_persistent(l_Lean_instInhabitedDeclarationLocation);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_DeclarationRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Position(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_DeclarationRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_DeclarationRange(builtin);
}
