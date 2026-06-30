// Lean compiler output
// Module: Lean.ToExpr
// Imports: Lean.ToLevel Init.Data.Rat.Basic
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_int_dec_le, lean_int_neg, lean_int8_dec_le,
    lean_int8_of_nat, lean_int8_to_int, lean_int16_dec_le, lean_int16_of_nat, lean_int16_to_int,
    lean_int32_dec_le, lean_int32_of_nat, lean_int32_to_int, lean_int64_dec_le, lean_int64_of_nat,
    lean_int64_to_int_sint, lean_isize_dec_le, lean_isize_of_nat, lean_isize_to_int, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
    lean_panic_fn_borrowed, lean_string_append, lean_uint8_to_nat, lean_uint16_to_nat,
    lean_uint32_to_nat, lean_uint64_to_nat, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Rat::Basic::{
    initialize_Init_Data_Rat_Basic, runtime_initialize_Init_Data_Rat_Basic,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_lit___override,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkAppB,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkRawNatLit, l_Lean_mkStrLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::ToLevel::{initialize_Lean_ToLevel, runtime_initialize_Lean_ToLevel};
pub static l_Lean_instToExprNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkNatLit as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprNat___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToExprNat___closed__1_value: leanh::LeanStringObject<4> =
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
static mut l_Lean_instToExprNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprNat___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_instToExprNat___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprNat___closed__1_value)
                as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprNat___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprNat___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprNat___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprNat___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprNat___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprNat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprInt_mkNat___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [79, 102, 78, 97, 116, 0],
    };
static mut l_Lean_instToExprInt_mkNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt_mkNat___closed__1_value: leanh::LeanStringObject<6> =
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
        m_data: [111, 102, 78, 97, 116, 0],
    };
static mut l_Lean_instToExprInt_mkNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprInt_mkNat___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            17636616155771105671 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt_mkNat___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__1_value)
                as *mut leanh::LeanObject,
            15578568367168711682 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt_mkNat___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt_mkNat___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt_mkNat___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt_mkNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt_mkNat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt_mkNat___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt_mkNat___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt_mkNat___closed__6_value: leanh::LeanStringObject<4> =
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
static mut l_Lean_instToExprInt_mkNat___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt_mkNat___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__6_value)
                as *mut leanh::LeanObject,
            7009148538150066493 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt_mkNat___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt_mkNat___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt_mkNat___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt_mkNat___closed__9_value: leanh::LeanStringObject<10> =
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
        m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 0],
    };
static mut l_Lean_instToExprInt_mkNat___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt_mkNat___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            10588691866721272861 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt_mkNat___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt_mkNat___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt_mkNat___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt___lam__0___closed__1_value: leanh::LeanStringObject<4> =
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
static mut l_Lean_instToExprInt___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt___lam__0___closed__2_value: leanh::LeanStringObject<4> =
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
static mut l_Lean_instToExprInt___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprInt___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            9626815015619986526 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
            17185717442815859305 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt___lam__0___closed__5_value: leanh::LeanStringObject<11> =
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
static mut l_Lean_instToExprInt___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprInt___lam__0___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__6_value)
                as *mut leanh::LeanObject,
            7009148538150066493 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt___lam__0___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__5_value)
                as *mut leanh::LeanObject,
            6362876895233142233 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprInt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprRat_mkNat___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [82, 97, 116, 0],
    };
static mut l_Lean_instToExprRat_mkNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprRat_mkNat___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            3708748166848919527 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprRat_mkNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprRat_mkNat___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat_mkNat___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprRat_mkNat___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            3708748166848919527 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprRat_mkNat___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            364901008092935897 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprRat_mkNat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprRat_mkNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat_mkNat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprRat_mkInt___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 110, 115, 116, 78, 101, 103, 0],
    };
static mut l_Lean_instToExprRat_mkInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprRat_mkInt___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            3708748166848919527 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprRat_mkInt___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__0_value)
                as *mut leanh::LeanObject,
            17656645524672112204 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprRat_mkInt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprRat_mkInt___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat_mkInt___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprRat___lam__0___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [72, 68, 105, 118, 0],
    };
static mut l_Lean_instToExprRat___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprRat___lam__0___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [104, 68, 105, 118, 0],
    };
static mut l_Lean_instToExprRat___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprRat___lam__0___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            11858238400308895562 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprRat___lam__0___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            6100819061652633370 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprRat___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprRat___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprRat___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprRat___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprRat___lam__0___closed__6_value: leanh::LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 68, 105, 118, 0],
    };
static mut l_Lean_instToExprRat___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprRat___lam__0___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__6_value)
                as *mut leanh::LeanObject,
            1334142589224437282 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprRat___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprRat___lam__0___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprRat___lam__0___closed__9_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 110, 115, 116, 68, 105, 118, 0],
    };
static mut l_Lean_instToExprRat___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprRat___lam__0___closed__10_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            3708748166848919527 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprRat___lam__0___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__10_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__9_value)
                as *mut leanh::LeanObject,
            16847769216878551944 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprRat___lam__0___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___lam__0___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprRat___lam__0___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat___lam__0___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprRat___lam__0___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat___lam__0___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprRat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprRat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprRat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprRat___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprRat___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprRat___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprRat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprFin___lam__0___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [70, 105, 110, 0],
    };
static mut l_Lean_instToExprFin___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprFin___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            15815496672699636542 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprFin___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprFin___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFin___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprFin___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            15815496672699636542 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprFin___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            6045136802442138716 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprFin___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprFin___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFin___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprFin___lam__0___closed__5_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
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
            105, 110, 115, 116, 78, 101, 90, 101, 114, 111, 83, 117, 99, 99, 0,
        ],
    };
static mut l_Lean_instToExprFin___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprFin___lam__0___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprNat___closed__1_value)
                as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprFin___lam__0___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__5_value)
                as *mut leanh::LeanObject,
            10810852250111692195 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprFin___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFin___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprFin___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFin___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprBitVec___lam__0___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [66, 105, 116, 86, 101, 99, 0],
    };
static mut l_Lean_instToExprBitVec___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBitVec___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprBitVec___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBitVec___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            5394957827732845164 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprBitVec___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBitVec___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__1_value)
                as *mut leanh::LeanObject,
            7578295756008745317 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprBitVec___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBitVec___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprBitVec___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprBitVec___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprBitVec___closed__0_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBitVec___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            5394957827732845164 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprBitVec___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBitVec___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprBitVec___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprBitVec___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprUInt8___lam__0___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [85, 73, 110, 116, 56, 0],
    };
static mut l_Lean_instToExprUInt8___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt8___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprUInt8___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt8___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            15764114953608429200 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt8___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt8___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt8___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt8___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprUInt8___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt8___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            15764114953608429200 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprUInt8___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt8___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            1458943469631247978 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt8___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt8___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt8___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt8___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprUInt8___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprUInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt8___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt8___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt8___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprUInt8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprUInt16___lam__0___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [85, 73, 110, 116, 49, 54, 0],
    };
static mut l_Lean_instToExprUInt16___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt16___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprUInt16___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt16___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            9755723410228041222 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt16___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt16___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt16___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt16___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprUInt16___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt16___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            9755723410228041222 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprUInt16___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt16___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            16668572274245391716 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt16___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt16___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt16___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt16___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprUInt16___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprUInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt16___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt16___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt16___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprUInt16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprUInt32___lam__0___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [85, 73, 110, 116, 51, 50, 0],
    };
static mut l_Lean_instToExprUInt32___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt32___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprUInt32___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt32___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            13474504806189678690 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt32___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt32___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt32___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt32___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprUInt32___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt32___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            13474504806189678690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprUInt32___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt32___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            16173759620455419504 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt32___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt32___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt32___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt32___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprUInt32___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprUInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt32___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt32___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt32___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprUInt32: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprUInt64___lam__0___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [85, 73, 110, 116, 54, 52, 0],
    };
static mut l_Lean_instToExprUInt64___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt64___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprUInt64___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt64___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            2954612489107370298 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt64___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt64___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt64___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt64___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprUInt64___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt64___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            2954612489107370298 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprUInt64___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUInt64___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            532958730868083720 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUInt64___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt64___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt64___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt64___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprUInt64___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUInt64___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprUInt64___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUInt64___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprUInt64: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprUSize___lam__0___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [85, 83, 105, 122, 101, 0],
    };
static mut l_Lean_instToExprUSize___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUSize___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprUSize___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUSize___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            17712594561405737325 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUSize___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUSize___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUSize___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUSize___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprUSize___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUSize___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            17712594561405737325 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprUSize___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUSize___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            17821382941423278891 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUSize___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUSize___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUSize___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUSize___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprUSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUSize___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprUSize___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUSize___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprUSize: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprInt8_mkNat___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [73, 110, 116, 56, 0],
    };
static mut l_Lean_instToExprInt8_mkNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt8_mkNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt8_mkNat___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt8_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            4828225126264449809 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt8_mkNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt8_mkNat___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt8_mkNat___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt8_mkNat___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprInt8_mkNat___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt8_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            4828225126264449809 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt8_mkNat___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt8_mkNat___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            15349045030394927999 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt8_mkNat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt8_mkNat___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt8_mkNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt8_mkNat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt8___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt8___lam__0___closed__0: u8 = 0;
static l_Lean_instToExprInt8___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt8_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            4828225126264449809 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt8___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt8___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__0_value)
                as *mut leanh::LeanObject,
            4682620960802703410 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt8___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt8___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt8___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt8___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt8___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt8___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt8___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt8___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprInt8___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt8___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprInt8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprInt16_mkNat___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [73, 110, 116, 49, 54, 0],
    };
static mut l_Lean_instToExprInt16_mkNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt16_mkNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt16_mkNat___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt16_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            1593258566177356093 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt16_mkNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt16_mkNat___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt16_mkNat___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt16_mkNat___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprInt16_mkNat___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt16_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            1593258566177356093 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt16_mkNat___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt16_mkNat___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            4116901328540829467 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt16_mkNat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt16_mkNat___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt16_mkNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt16_mkNat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt16___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt16___lam__0___closed__0: u16 = 0;
static l_Lean_instToExprInt16___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt16_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            1593258566177356093 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt16___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt16___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__0_value)
                as *mut leanh::LeanObject,
            12385669288801998142 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt16___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt16___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt16___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt16___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt16___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt16___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt16___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt16___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt16___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt16___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprInt16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprInt32_mkNat___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [73, 110, 116, 51, 50, 0],
    };
static mut l_Lean_instToExprInt32_mkNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt32_mkNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt32_mkNat___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt32_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            17423969607579146442 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt32_mkNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt32_mkNat___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt32_mkNat___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt32_mkNat___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprInt32_mkNat___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt32_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            17423969607579146442 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt32_mkNat___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt32_mkNat___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            12916542796336326136 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt32_mkNat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt32_mkNat___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt32_mkNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt32_mkNat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt32___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt32___lam__0___closed__0: u32 = 0;
static l_Lean_instToExprInt32___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt32_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            17423969607579146442 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt32___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt32___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__0_value)
                as *mut leanh::LeanObject,
            16834749042409166469 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt32___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt32___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt32___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt32___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt32___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt32___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt32___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt32___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt32___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt32___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprInt32: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprInt64_mkNat___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [73, 110, 116, 54, 52, 0],
    };
static mut l_Lean_instToExprInt64_mkNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt64_mkNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprInt64_mkNat___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt64_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            6508593840631735363 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt64_mkNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt64_mkNat___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt64_mkNat___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt64_mkNat___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprInt64_mkNat___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt64_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            6508593840631735363 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt64_mkNat___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt64_mkNat___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            12348351689620486501 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt64_mkNat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt64_mkNat___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt64_mkNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt64_mkNat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt64___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt64___lam__0___closed__0: u64 = 0;
static l_Lean_instToExprInt64___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt64_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            6508593840631735363 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprInt64___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprInt64___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__0_value)
                as *mut leanh::LeanObject,
            6649467428781922328 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprInt64___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt64___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt64___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt64___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprInt64___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprInt64___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprInt64___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt64___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprInt64___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprInt64___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprInt64: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprISize_mkNat___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [73, 83, 105, 122, 101, 0],
    };
static mut l_Lean_instToExprISize_mkNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprISize_mkNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprISize_mkNat___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprISize_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            16021149375362053230 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprISize_mkNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprISize_mkNat___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprISize_mkNat___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprISize_mkNat___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprISize_mkNat___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprISize_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            16021149375362053230 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprISize_mkNat___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprISize_mkNat___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__9_value)
                as *mut leanh::LeanObject,
            10790860098991891820 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprISize_mkNat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprISize_mkNat___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprISize_mkNat___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprISize_mkNat___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprISize___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprISize___lam__0___closed__0: usize = 0;
static l_Lean_instToExprISize___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprISize_mkNat___closed__0_value)
                as *mut leanh::LeanObject,
            16021149375362053230 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprISize___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprISize___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprRat_mkInt___closed__0_value)
                as *mut leanh::LeanObject,
            13329398572434340025 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprISize___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprISize___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprISize___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprISize___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprISize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprISize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprISize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprISize___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprISize___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprISize___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprISize___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprISize___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprISize: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprBool___lam__0___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_instToExprBool___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprBool___lam__0___closed__1_value: leanh::LeanStringObject<6> =
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
static mut l_Lean_instToExprBool___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprBool___lam__0___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprBool___lam__0___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            15761733860085307253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprBool___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprBool___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprBool___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprBool___lam__0___closed__4_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_instToExprBool___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprBool___lam__0___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprBool___lam__0___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__4_value)
                as *mut leanh::LeanObject,
            9255189395584251158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprBool___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprBool___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprBool___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprBool___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBool___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToExprBool___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprBool___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprBool___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprBool___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprBool___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprBool___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprBool___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprBool___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprBool: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprChar___lam__0___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [67, 104, 97, 114, 0],
    };
static mut l_Lean_instToExprChar___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprChar___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprChar___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprChar___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprChar___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprChar___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprInt_mkNat___closed__1_value)
                as *mut leanh::LeanObject,
            18098914779984442139 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprChar___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprChar___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprChar___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprChar___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprChar___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprChar___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprChar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprChar___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToExprChar___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprChar___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprChar___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprChar___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprChar___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprChar___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprChar___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprChar___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprChar: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkStrLit as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprString___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToExprString___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lean_instToExprString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprString___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_instToExprString___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprString___closed__1_value)
                as *mut leanh::LeanObject,
            3136308715950998022 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprString___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprString___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprString___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprString___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprString___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprString: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprUnit___lam__0___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [85, 110, 105, 116, 0],
    };
static mut l_Lean_instToExprUnit___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUnit___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprUnit___lam__0___closed__1_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_instToExprUnit___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUnit___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprUnit___lam__0___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUnit___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            9833841078580172006 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprUnit___lam__0___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUnit___lam__0___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprUnit___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            565778312915565143 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUnit___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUnit___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprUnit___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUnit___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprUnit___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprUnit___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprUnit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUnit___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instToExprUnit___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprUnit___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            9833841078580172006 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprUnit___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprUnit___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprUnit___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUnit___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprUnit___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprUnit___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprUnit: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprFilePath___lam__0___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [83, 121, 115, 116, 101, 109, 0],
    };
static mut l_Lean_instToExprFilePath___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprFilePath___lam__0___closed__1_value: leanh::LeanStringObject<9> =
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
        m_data: [70, 105, 108, 101, 80, 97, 116, 104, 0],
    };
static mut l_Lean_instToExprFilePath___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprFilePath___lam__0___closed__2_value: leanh::LeanStringObject<3> =
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
static mut l_Lean_instToExprFilePath___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            3794196532276496372 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            16862427096323398393 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprFilePath___lam__0___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
            12740738272846701813 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprFilePath___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprFilePath___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFilePath___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprFilePath___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprFilePath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFilePath___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprFilePath___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            3794196532276496372 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprFilePath___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFilePath___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            16862427096323398393 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprFilePath___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFilePath___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprFilePath___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFilePath___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprFilePath___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFilePath___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprFilePath: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value:
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
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value:
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
    m_data: [78, 97, 109, 101, 0],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value)
        as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value:
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
            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value)
            as *mut leanh::LeanObject,
        13306843946249674491 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3_value:
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
    m_data: [109, 107, 83, 116, 114, 0],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [76, 101, 97, 110, 46, 84, 111, 69, 120, 112, 114, 0],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 84, 111, 69, 120, 112, 114,
        46, 48, 46, 76, 101, 97, 110, 46, 78, 97, 109, 101, 46, 116, 111, 69, 120, 112, 114, 65,
        117, 120, 46, 109, 107, 83, 116, 114, 0,
    ],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 0],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0_value)
        as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_1:
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
            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value)
            as *mut leanh::LeanObject,
        13306843946249674491 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value:
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
            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0_value)
            as *mut leanh::LeanObject,
        8742792063936078747 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3_value:
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
    m_data: [115, 116, 114, 0],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3_value)
        as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_1:
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
            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value)
            as *mut leanh::LeanObject,
        13306843946249674491 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value:
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
            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3_value)
            as *mut leanh::LeanObject,
        8392322758047580095 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6_value:
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
    m_data: [110, 117, 109, 0],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6_value)
        as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_1:
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
            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value)
            as *mut leanh::LeanObject,
        13306843946249674491 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value:
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
            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6_value)
            as *mut leanh::LeanObject,
        7229350633979142691 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprName___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprName___private__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprName___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprName___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprName___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instToExprName___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprName___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instToExprName: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [79, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        18184376426117065311 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value:
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
            l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        9480010471355609749 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3_value:
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
    m_data: [115, 111, 109, 101, 0],
};
static mut l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        18184376426117065311 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value:
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
            l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3_value)
            as *mut leanh::LeanObject,
        4893146552088433753 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprOptionOfToLevel___redArg___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        18184376426117065311 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprOptionOfToLevel___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprOptionOfToLevel___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprListOfToLevel___redArg___closed__0_value:
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
    m_data: [76, 105, 115, 116, 0],
};
static mut l_Lean_instToExprListOfToLevel___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprListOfToLevel___redArg___closed__1_value:
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
    m_data: [110, 105, 108, 0],
};
static mut l_Lean_instToExprListOfToLevel___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprListOfToLevel___redArg___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprListOfToLevel___redArg___closed__2_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        18135193680607614554 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprListOfToLevel___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprListOfToLevel___redArg___closed__3_value:
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
    m_data: [99, 111, 110, 115, 0],
};
static mut l_Lean_instToExprListOfToLevel___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprListOfToLevel___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprListOfToLevel___redArg___closed__4_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        8614124190858717794 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprListOfToLevel___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprListOfToLevel___redArg___closed__5_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprListOfToLevel___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0_value:
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
    m_data: [116, 111, 65, 114, 114, 97, 121, 0],
};
static mut l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_instToExprListOfToLevel___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value:
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
            l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        8414467900391110369 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprArrayOfToLevel___redArg___closed__0_value:
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
    m_data: [65, 114, 114, 97, 121, 0],
};
static mut l_Lean_instToExprArrayOfToLevel___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprArrayOfToLevel___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprArrayOfToLevel___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_instToExprArrayOfToLevel___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        8749134177695247953 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprArrayOfToLevel___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprArrayOfToLevel___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value:
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
    m_data: [80, 114, 111, 100, 0],
};
static mut l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        15289851429949568889 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value:
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
            l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        6466355875042130293 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprProdOfToLevel___redArg___closed__0_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        15289851429949568889 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprProdOfToLevel___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprProdOfToLevel___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprLiteral___lam__0___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [76, 105, 116, 101, 114, 97, 108, 0],
    };
static mut l_Lean_instToExprLiteral___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprLiteral___lam__0___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [110, 97, 116, 86, 97, 108, 0],
    };
static mut l_Lean_instToExprLiteral___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value
            ) as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            7001815944269665831 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprLiteral___lam__0___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            9295767770006931264 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprLiteral___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprLiteral___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprLiteral___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprLiteral___lam__0___closed__4_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 116, 114, 86, 97, 108, 0],
    };
static mut l_Lean_instToExprLiteral___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value
            ) as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            7001815944269665831 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprLiteral___lam__0___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__4_value)
                as *mut leanh::LeanObject,
            2005404019190257220 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprLiteral___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprLiteral___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprLiteral___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprLiteral___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprLiteral___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprLiteral___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprLiteral___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprLiteral___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value
            ) as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprLiteral___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprLiteral___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprLiteral___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            7001815944269665831 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprLiteral___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprLiteral___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprLiteral___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprLiteral___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprLiteral___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprLiteral___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprLiteral: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprFVarId___lam__0___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [70, 86, 97, 114, 73, 100, 0],
    };
static mut l_Lean_instToExprFVarId___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFVarId___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value
            ) as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprFVarId___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            6212595679582900358 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprFVarId___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprFilePath___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
            6968149084986791158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprFVarId___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFVarId___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprFVarId___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFVarId___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprFVarId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instToExprFVarId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToExprFVarId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFVarId___closed__0_value) as *mut leanh::LeanObject;
static l_Lean_instToExprFVarId___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value
            ) as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprFVarId___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprFVarId___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprFVarId___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            6212595679582900358 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprFVarId___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprFVarId___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_instToExprFVarId___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFVarId___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprFVarId___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprFVarId___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprFVarId: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instToExprPreresolved___lam__0___closed__0_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [83, 121, 110, 116, 97, 120, 0],
};
static mut l_Lean_instToExprPreresolved___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprPreresolved___lam__0___closed__1_value: leanh::LeanStringObject<
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
    m_data: [80, 114, 101, 114, 101, 115, 111, 108, 118, 101, 100, 0],
};
static mut l_Lean_instToExprPreresolved___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instToExprPreresolved___lam__0___closed__2_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 0],
};
static mut l_Lean_instToExprPreresolved___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        5337926038336999469 as *mut leanh::LeanObject,
    ],
};
static l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        9936810691482186699 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprPreresolved___lam__0___closed__3_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        15189601143227046797 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprPreresolved___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprPreresolved___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprPreresolved___lam__0___closed__5_value: leanh::LeanStringObject<
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
    m_data: [100, 101, 99, 108, 0],
};
static mut l_Lean_instToExprPreresolved___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        5337926038336999469 as *mut leanh::LeanObject,
    ],
};
static l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        9936810691482186699 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_instToExprPreresolved___lam__0___closed__6_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__5_value)
            as *mut leanh::LeanObject,
        9797095687668378378 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprPreresolved___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprPreresolved___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instToExprPreresolved___lam__0___closed__8_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instToExprPreresolved___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprPreresolved___lam__0___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___lam__0___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprPreresolved___lam__0___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___lam__0___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprPreresolved___lam__0___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___lam__0___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprPreresolved___lam__0___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___lam__0___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprPreresolved___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_instToExprPreresolved___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value
            ) as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_instToExprPreresolved___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprPreresolved___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            5337926038336999469 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_instToExprPreresolved___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instToExprPreresolved___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToExprPreresolved___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            9936810691482186699 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instToExprPreresolved___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToExprPreresolved___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instToExprPreresolved___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instToExprPreresolved___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instToExprPreresolved___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instToExprPreresolved: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_instToExprNat___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1209_ = leanh::lean_box(0);
    v___x_1210_ = l_Lean_instToExprNat___closed__2;
    v___x_1211_ = l_Lean_mkConst(v___x_1210_, v___x_1209_);
    return v___x_1211_;
}
pub unsafe fn _init_l_Lean_instToExprNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1212_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprNat___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprNat___closed__3_once),
        _init_l_Lean_instToExprNat___closed__3,
    );
    v___x_1213_ = l_Lean_instToExprNat___closed__0;
    v___x_1214_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1213_);
    leanh::lean_ctor_set(v___x_1214_, 1, v___x_1212_);
    return v___x_1214_;
}
pub unsafe fn _init_l_Lean_instToExprNat() -> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprNat___closed__4_once),
        _init_l_Lean_instToExprNat___closed__4,
    );
    return v___x_1215_;
}
pub unsafe fn _init_l_Lean_instToExprInt_mkNat___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = leanh::lean_unsigned_to_nat(0);
    v___x_1222_ = l_Lean_Level_ofNat(v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn _init_l_Lean_instToExprInt_mkNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1223_ = leanh::lean_box(0);
    v___x_1224_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__3_once),
        _init_l_Lean_instToExprInt_mkNat___closed__3,
    );
    v___x_1225_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1225_, 0, v___x_1224_);
    leanh::lean_ctor_set(v___x_1225_, 1, v___x_1223_);
    return v___x_1225_;
}
pub unsafe fn _init_l_Lean_instToExprInt_mkNat___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1226_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt_mkNat___closed__4,
    );
    v___x_1227_ = l_Lean_instToExprInt_mkNat___closed__2;
    v___x_1228_ = l_Lean_Expr_const___override(v___x_1227_, v___x_1226_);
    return v___x_1228_;
}
pub unsafe fn _init_l_Lean_instToExprInt_mkNat___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = leanh::lean_box(0);
    v___x_1233_ = l_Lean_instToExprInt_mkNat___closed__7;
    v___x_1234_ = l_Lean_Expr_const___override(v___x_1233_, v___x_1232_);
    return v___x_1234_;
}
pub unsafe fn _init_l_Lean_instToExprInt_mkNat___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = leanh::lean_box(0);
    v___x_1239_ = l_Lean_instToExprInt_mkNat___closed__10;
    v___x_1240_ = l_Lean_Expr_const___override(v___x_1239_, v___x_1238_);
    return v___x_1240_;
}
pub unsafe fn l_Lean_instToExprInt_mkNat(
    mut v_n_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1242_ = l_Lean_mkRawNatLit(v_n_1241_);
    v___x_1243_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1244_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__8),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__8_once),
        _init_l_Lean_instToExprInt_mkNat___closed__8,
    );
    v___x_1245_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__11),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__11_once),
        _init_l_Lean_instToExprInt_mkNat___closed__11,
    );
    leanh::lean_inc_ref(v_r_1242_);
    v___x_1246_ = l_Lean_Expr_app___override(v___x_1245_, v_r_1242_);
    v___x_1247_ = l_Lean_mkApp3(v___x_1243_, v___x_1244_, v_r_1242_, v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn _init_l_Lean_instToExprInt___lam__0___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1248_ = leanh::lean_unsigned_to_nat(0);
    v___x_1249_ = lean_nat_to_int(v___x_1248_);
    return v___x_1249_;
}
pub unsafe fn _init_l_Lean_instToExprInt___lam__0___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt_mkNat___closed__4,
    );
    v___x_1256_ = l_Lean_instToExprInt___lam__0___closed__3;
    v___x_1257_ = l_Lean_Expr_const___override(v___x_1256_, v___x_1255_);
    return v___x_1257_;
}
pub unsafe fn _init_l_Lean_instToExprInt___lam__0___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = leanh::lean_box(0);
    v___x_1263_ = l_Lean_instToExprInt___lam__0___closed__6;
    v___x_1264_ = l_Lean_Expr_const___override(v___x_1263_, v___x_1262_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_instToExprInt___lam__0(
    mut v_i_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    v___x_1266_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__0_once),
        _init_l_Lean_instToExprInt___lam__0___closed__0,
    );
    v___x_1267_ = lean_int_dec_le(v___x_1266_, v_i_1265_);
    if v___x_1267_ == 0 {
        let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1268_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4_once),
            _init_l_Lean_instToExprInt___lam__0___closed__4,
        );
        v___x_1269_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__8),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__8_once),
            _init_l_Lean_instToExprInt_mkNat___closed__8,
        );
        v___x_1270_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__7),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__7_once),
            _init_l_Lean_instToExprInt___lam__0___closed__7,
        );
        v___x_1271_ = lean_int_neg(v_i_1265_);
        v___x_1272_ = l_Int_toNat(v___x_1271_);
        leanh::lean_dec(v___x_1271_);
        v___x_1273_ = l_Lean_instToExprInt_mkNat(v___x_1272_);
        v___x_1274_ = l_Lean_mkApp3(v___x_1268_, v___x_1269_, v___x_1270_, v___x_1273_);
        return v___x_1274_;
    } else {
        let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1275_ = l_Int_toNat(v_i_1265_);
        v___x_1276_ = l_Lean_instToExprInt_mkNat(v___x_1275_);
        return v___x_1276_;
    }
}
pub unsafe fn l_Lean_instToExprInt___lam__0___boxed(
    mut v_i_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Lean_instToExprInt___lam__0(v_i_1277_);
    leanh::lean_dec(v_i_1277_);
    return v_res_1278_;
}
pub unsafe fn _init_l_Lean_instToExprInt___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__8),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__8_once),
        _init_l_Lean_instToExprInt_mkNat___closed__8,
    );
    v___f_1281_ = l_Lean_instToExprInt___closed__0;
    v___x_1282_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1282_, 0, v___f_1281_);
    leanh::lean_ctor_set(v___x_1282_, 1, v___x_1280_);
    return v___x_1282_;
}
pub unsafe fn _init_l_Lean_instToExprInt() -> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt___closed__1_once),
        _init_l_Lean_instToExprInt___closed__1,
    );
    return v___x_1283_;
}
pub unsafe fn _init_l_Lean_instToExprRat_mkNat___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = leanh::lean_box(0);
    v___x_1288_ = l_Lean_instToExprRat_mkNat___closed__1;
    v___x_1289_ = l_Lean_Expr_const___override(v___x_1288_, v___x_1287_);
    return v___x_1289_;
}
pub unsafe fn _init_l_Lean_instToExprRat_mkNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1293_ = leanh::lean_box(0);
    v___x_1294_ = l_Lean_instToExprRat_mkNat___closed__3;
    v___x_1295_ = l_Lean_Expr_const___override(v___x_1294_, v___x_1293_);
    return v___x_1295_;
}
pub unsafe fn l_Lean_instToExprRat_mkNat(
    mut v_n_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1297_ = l_Lean_mkRawNatLit(v_n_1296_);
    v___x_1298_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1299_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2_once),
        _init_l_Lean_instToExprRat_mkNat___closed__2,
    );
    v___x_1300_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__4_once),
        _init_l_Lean_instToExprRat_mkNat___closed__4,
    );
    leanh::lean_inc_ref(v_r_1297_);
    v___x_1301_ = l_Lean_Expr_app___override(v___x_1300_, v_r_1297_);
    v___x_1302_ = l_Lean_mkApp3(v___x_1298_, v___x_1299_, v_r_1297_, v___x_1301_);
    return v___x_1302_;
}
pub unsafe fn _init_l_Lean_instToExprRat_mkInt___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1307_ = leanh::lean_box(0);
    v___x_1308_ = l_Lean_instToExprRat_mkInt___closed__1;
    v___x_1309_ = l_Lean_Expr_const___override(v___x_1308_, v___x_1307_);
    return v___x_1309_;
}
pub unsafe fn l_Lean_instToExprRat_mkInt(
    mut v_i_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    v___x_1311_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__0_once),
        _init_l_Lean_instToExprInt___lam__0___closed__0,
    );
    v___x_1312_ = lean_int_dec_le(v___x_1311_, v_i_1310_);
    if v___x_1312_ == 0 {
        let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1313_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4_once),
            _init_l_Lean_instToExprInt___lam__0___closed__4,
        );
        v___x_1314_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2_once),
            _init_l_Lean_instToExprRat_mkNat___closed__2,
        );
        v___x_1315_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkInt___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkInt___closed__2_once),
            _init_l_Lean_instToExprRat_mkInt___closed__2,
        );
        v___x_1316_ = lean_int_neg(v_i_1310_);
        v___x_1317_ = l_Int_toNat(v___x_1316_);
        leanh::lean_dec(v___x_1316_);
        v___x_1318_ = l_Lean_instToExprRat_mkNat(v___x_1317_);
        v___x_1319_ = l_Lean_mkApp3(v___x_1313_, v___x_1314_, v___x_1315_, v___x_1318_);
        return v___x_1319_;
    } else {
        let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1320_ = l_Int_toNat(v_i_1310_);
        v___x_1321_ = l_Lean_instToExprRat_mkNat(v___x_1320_);
        return v___x_1321_;
    }
}
pub unsafe fn l_Lean_instToExprRat_mkInt___boxed(
    mut v_i_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1323_ = l_Lean_instToExprRat_mkInt(v_i_1322_);
    leanh::lean_dec(v_i_1322_);
    return v_res_1323_;
}
pub unsafe fn _init_l_Lean_instToExprRat___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt_mkNat___closed__4,
    );
    v___x_1330_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__3_once),
        _init_l_Lean_instToExprInt_mkNat___closed__3,
    );
    v___x_1331_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1331_, 0, v___x_1330_);
    leanh::lean_ctor_set(v___x_1331_, 1, v___x_1329_);
    return v___x_1331_;
}
pub unsafe fn _init_l_Lean_instToExprRat___lam__0___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__3_once),
        _init_l_Lean_instToExprRat___lam__0___closed__3,
    );
    v___x_1333_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__3_once),
        _init_l_Lean_instToExprInt_mkNat___closed__3,
    );
    v___x_1334_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1334_, 0, v___x_1333_);
    leanh::lean_ctor_set(v___x_1334_, 1, v___x_1332_);
    return v___x_1334_;
}
pub unsafe fn _init_l_Lean_instToExprRat___lam__0___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__4_once),
        _init_l_Lean_instToExprRat___lam__0___closed__4,
    );
    v___x_1336_ = l_Lean_instToExprRat___lam__0___closed__2;
    v___x_1337_ = l_Lean_Expr_const___override(v___x_1336_, v___x_1335_);
    return v___x_1337_;
}
pub unsafe fn _init_l_Lean_instToExprRat___lam__0___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt_mkNat___closed__4,
    );
    v___x_1342_ = l_Lean_instToExprRat___lam__0___closed__7;
    v___x_1343_ = l_Lean_Expr_const___override(v___x_1342_, v___x_1341_);
    return v___x_1343_;
}
pub unsafe fn _init_l_Lean_instToExprRat___lam__0___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1348_ = leanh::lean_box(0);
    v___x_1349_ = l_Lean_instToExprRat___lam__0___closed__10;
    v___x_1350_ = l_Lean_Expr_const___override(v___x_1349_, v___x_1348_);
    return v___x_1350_;
}
pub unsafe fn _init_l_Lean_instToExprRat___lam__0___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__11),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__11_once),
        _init_l_Lean_instToExprRat___lam__0___closed__11,
    );
    v___x_1352_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2_once),
        _init_l_Lean_instToExprRat_mkNat___closed__2,
    );
    v___x_1353_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__8),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__8_once),
        _init_l_Lean_instToExprRat___lam__0___closed__8,
    );
    v___x_1354_ = l_Lean_mkAppB(v___x_1353_, v___x_1352_, v___x_1351_);
    return v___x_1354_;
}
pub unsafe fn l_Lean_instToExprRat___lam__0(
    mut v_i_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_num_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    v_num_1356_ = leanh::lean_ctor_get(v_i_1355_, 0);
    leanh::lean_inc(v_num_1356_);
    v_den_1357_ = leanh::lean_ctor_get(v_i_1355_, 1);
    leanh::lean_inc(v_den_1357_);
    leanh::lean_dec_ref(v_i_1355_);
    v___x_1358_ = leanh::lean_unsigned_to_nat(1);
    v___x_1359_ = lean_nat_dec_eq(v_den_1357_, v___x_1358_);
    if v___x_1359_ == 0 {
        let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1360_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__5),
            core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__5_once),
            _init_l_Lean_instToExprRat___lam__0___closed__5,
        );
        v___x_1361_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2_once),
            _init_l_Lean_instToExprRat_mkNat___closed__2,
        );
        v___x_1362_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__12),
            core::ptr::addr_of_mut!(l_Lean_instToExprRat___lam__0___closed__12_once),
            _init_l_Lean_instToExprRat___lam__0___closed__12,
        );
        v___x_1363_ = l_Lean_instToExprRat_mkInt(v_num_1356_);
        leanh::lean_dec(v_num_1356_);
        v___x_1364_ = lean_nat_to_int(v_den_1357_);
        v___x_1365_ = l_Lean_instToExprRat_mkInt(v___x_1364_);
        leanh::lean_dec(v___x_1364_);
        v___x_1366_ = l_Lean_mkApp6(
            v___x_1360_,
            v___x_1361_,
            v___x_1361_,
            v___x_1361_,
            v___x_1362_,
            v___x_1363_,
            v___x_1365_,
        );
        return v___x_1366_;
    } else {
        let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_den_1357_);
        v___x_1367_ = l_Lean_instToExprRat_mkInt(v_num_1356_);
        leanh::lean_dec(v_num_1356_);
        return v___x_1367_;
    }
}
pub unsafe fn _init_l_Lean_instToExprRat___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat_mkNat___closed__2_once),
        _init_l_Lean_instToExprRat_mkNat___closed__2,
    );
    v___f_1370_ = l_Lean_instToExprRat___closed__0;
    v___x_1371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1371_, 0, v___f_1370_);
    leanh::lean_ctor_set(v___x_1371_, 1, v___x_1369_);
    return v___x_1371_;
}
pub unsafe fn _init_l_Lean_instToExprRat() -> *mut leanh::LeanObject {
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprRat___closed__1_once),
        _init_l_Lean_instToExprRat___closed__1,
    );
    return v___x_1372_;
}
pub unsafe fn _init_l_Lean_instToExprFin___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = leanh::lean_box(0);
    v___x_1377_ = l_Lean_instToExprFin___lam__0___closed__1;
    v___x_1378_ = l_Lean_mkConst(v___x_1377_, v___x_1376_);
    return v___x_1378_;
}
pub unsafe fn _init_l_Lean_instToExprFin___lam__0___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = leanh::lean_box(0);
    v___x_1383_ = l_Lean_instToExprFin___lam__0___closed__3;
    v___x_1384_ = l_Lean_Expr_const___override(v___x_1383_, v___x_1382_);
    return v___x_1384_;
}
pub unsafe fn _init_l_Lean_instToExprFin___lam__0___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = leanh::lean_box(0);
    v___x_1390_ = l_Lean_instToExprFin___lam__0___closed__6;
    v___x_1391_ = l_Lean_Expr_const___override(v___x_1390_, v___x_1389_);
    return v___x_1391_;
}
pub unsafe fn l_Lean_instToExprFin___lam__0(
    mut v_n_1392_: *mut leanh::LeanObject,
    mut v_a_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1394_ = l_Lean_mkRawNatLit(v_a_1393_);
    v___x_1395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1396_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__2_once),
        _init_l_Lean_instToExprFin___lam__0___closed__2,
    );
    leanh::lean_inc(v_n_1392_);
    v___x_1397_ = l_Lean_mkNatLit(v_n_1392_);
    leanh::lean_inc_ref(v___x_1397_);
    v___x_1398_ = l_Lean_Expr_app___override(v___x_1396_, v___x_1397_);
    v___x_1399_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__4_once),
        _init_l_Lean_instToExprFin___lam__0___closed__4,
    );
    v___x_1400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__7_once),
        _init_l_Lean_instToExprFin___lam__0___closed__7,
    );
    v___x_1401_ = leanh::lean_unsigned_to_nat(1);
    v___x_1402_ = lean_nat_sub(v_n_1392_, v___x_1401_);
    leanh::lean_dec(v_n_1392_);
    v___x_1403_ = l_Lean_mkNatLit(v___x_1402_);
    v___x_1404_ = l_Lean_Expr_app___override(v___x_1400_, v___x_1403_);
    leanh::lean_inc_ref(v_r_1394_);
    v___x_1405_ = l_Lean_mkApp3(v___x_1399_, v___x_1397_, v___x_1404_, v_r_1394_);
    v___x_1406_ = l_Lean_mkApp3(v___x_1395_, v___x_1398_, v_r_1394_, v___x_1405_);
    return v___x_1406_;
}
pub unsafe fn l_Lean_instToExprFin(
    mut v_n_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_n_1407_);
    v___f_1408_ = leanh::lean_alloc_closure(
        l_Lean_instToExprFin___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1408_, 0, v_n_1407_);
    v___x_1409_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprFin___lam__0___closed__2_once),
        _init_l_Lean_instToExprFin___lam__0___closed__2,
    );
    v___x_1410_ = l_Lean_mkNatLit(v_n_1407_);
    v___x_1411_ = l_Lean_Expr_app___override(v___x_1409_, v___x_1410_);
    v___x_1412_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1412_, 0, v___f_1408_);
    leanh::lean_ctor_set(v___x_1412_, 1, v___x_1411_);
    return v___x_1412_;
}
pub unsafe fn _init_l_Lean_instToExprBitVec___lam__0___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = leanh::lean_box(0);
    v___x_1418_ = l_Lean_instToExprBitVec___lam__0___closed__1;
    v___x_1419_ = l_Lean_Expr_const___override(v___x_1418_, v___x_1417_);
    return v___x_1419_;
}
pub unsafe fn l_Lean_instToExprBitVec___lam__0(
    mut v_n_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprBitVec___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprBitVec___lam__0___closed__2_once),
        _init_l_Lean_instToExprBitVec___lam__0___closed__2,
    );
    v___x_1423_ = l_Lean_mkNatLit(v_n_1420_);
    v___x_1424_ = l_Lean_mkNatLit(v_a_1421_);
    v___x_1425_ = l_Lean_mkAppB(v___x_1422_, v___x_1423_, v___x_1424_);
    return v___x_1425_;
}
pub unsafe fn _init_l_Lean_instToExprBitVec___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = leanh::lean_box(0);
    v___x_1429_ = l_Lean_instToExprBitVec___closed__0;
    v___x_1430_ = l_Lean_mkConst(v___x_1429_, v___x_1428_);
    return v___x_1430_;
}
pub unsafe fn l_Lean_instToExprBitVec(
    mut v_n_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_n_1431_);
    v___f_1432_ = leanh::lean_alloc_closure(
        l_Lean_instToExprBitVec___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1432_, 0, v_n_1431_);
    v___x_1433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprBitVec___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprBitVec___closed__1_once),
        _init_l_Lean_instToExprBitVec___closed__1,
    );
    v___x_1434_ = l_Lean_mkNatLit(v_n_1431_);
    v___x_1435_ = l_Lean_Expr_app___override(v___x_1433_, v___x_1434_);
    v___x_1436_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1436_, 0, v___f_1432_);
    leanh::lean_ctor_set(v___x_1436_, 1, v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn _init_l_Lean_instToExprUInt8___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1440_ = leanh::lean_box(0);
    v___x_1441_ = l_Lean_instToExprUInt8___lam__0___closed__1;
    v___x_1442_ = l_Lean_mkConst(v___x_1441_, v___x_1440_);
    return v___x_1442_;
}
pub unsafe fn _init_l_Lean_instToExprUInt8___lam__0___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = leanh::lean_box(0);
    v___x_1447_ = l_Lean_instToExprUInt8___lam__0___closed__3;
    v___x_1448_ = l_Lean_Expr_const___override(v___x_1447_, v___x_1446_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_instToExprUInt8___lam__0(mut v_a_1449_: u8) -> *mut leanh::LeanObject {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = lean_uint8_to_nat(v_a_1449_);
    v_r_1451_ = l_Lean_mkRawNatLit(v___x_1450_);
    v___x_1452_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1453_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt8___lam__0___closed__2,
    );
    v___x_1454_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___lam__0___closed__4_once),
        _init_l_Lean_instToExprUInt8___lam__0___closed__4,
    );
    leanh::lean_inc_ref(v_r_1451_);
    v___x_1455_ = l_Lean_Expr_app___override(v___x_1454_, v_r_1451_);
    v___x_1456_ = l_Lean_mkApp3(v___x_1452_, v___x_1453_, v_r_1451_, v___x_1455_);
    return v___x_1456_;
}
pub unsafe fn l_Lean_instToExprUInt8___lam__0___boxed(
    mut v_a_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1458_: u8 = 0;
    let mut v_res_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1458_ = (leanh::lean_unbox(v_a_1457_) as u8);
    v_res_1459_ = l_Lean_instToExprUInt8___lam__0(v_a_boxed_1458_);
    return v_res_1459_;
}
pub unsafe fn _init_l_Lean_instToExprUInt8___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1461_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt8___lam__0___closed__2,
    );
    v___f_1462_ = l_Lean_instToExprUInt8___closed__0;
    v___x_1463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1463_, 0, v___f_1462_);
    leanh::lean_ctor_set(v___x_1463_, 1, v___x_1461_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lean_instToExprUInt8() -> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt8___closed__1_once),
        _init_l_Lean_instToExprUInt8___closed__1,
    );
    return v___x_1464_;
}
pub unsafe fn _init_l_Lean_instToExprUInt16___lam__0___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1468_ = leanh::lean_box(0);
    v___x_1469_ = l_Lean_instToExprUInt16___lam__0___closed__1;
    v___x_1470_ = l_Lean_mkConst(v___x_1469_, v___x_1468_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_instToExprUInt16___lam__0___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = leanh::lean_box(0);
    v___x_1475_ = l_Lean_instToExprUInt16___lam__0___closed__3;
    v___x_1476_ = l_Lean_Expr_const___override(v___x_1475_, v___x_1474_);
    return v___x_1476_;
}
pub unsafe fn l_Lean_instToExprUInt16___lam__0(
    mut v_a_1477_: u16,
) -> *mut leanh::LeanObject {
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = lean_uint16_to_nat(v_a_1477_);
    v_r_1479_ = l_Lean_mkRawNatLit(v___x_1478_);
    v___x_1480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt16___lam__0___closed__2,
    );
    v___x_1482_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___lam__0___closed__4_once),
        _init_l_Lean_instToExprUInt16___lam__0___closed__4,
    );
    leanh::lean_inc_ref(v_r_1479_);
    v___x_1483_ = l_Lean_Expr_app___override(v___x_1482_, v_r_1479_);
    v___x_1484_ = l_Lean_mkApp3(v___x_1480_, v___x_1481_, v_r_1479_, v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l_Lean_instToExprUInt16___lam__0___boxed(
    mut v_a_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1486_: u16 = 0;
    let mut v_res_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1486_ = (leanh::lean_unbox(v_a_1485_) as u16);
    v_res_1487_ = l_Lean_instToExprUInt16___lam__0(v_a_boxed_1486_);
    return v_res_1487_;
}
pub unsafe fn _init_l_Lean_instToExprUInt16___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt16___lam__0___closed__2,
    );
    v___f_1490_ = l_Lean_instToExprUInt16___closed__0;
    v___x_1491_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1491_, 0, v___f_1490_);
    leanh::lean_ctor_set(v___x_1491_, 1, v___x_1489_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_instToExprUInt16() -> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt16___closed__1_once),
        _init_l_Lean_instToExprUInt16___closed__1,
    );
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_instToExprUInt32___lam__0___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = leanh::lean_box(0);
    v___x_1497_ = l_Lean_instToExprUInt32___lam__0___closed__1;
    v___x_1498_ = l_Lean_mkConst(v___x_1497_, v___x_1496_);
    return v___x_1498_;
}
pub unsafe fn _init_l_Lean_instToExprUInt32___lam__0___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = leanh::lean_box(0);
    v___x_1503_ = l_Lean_instToExprUInt32___lam__0___closed__3;
    v___x_1504_ = l_Lean_Expr_const___override(v___x_1503_, v___x_1502_);
    return v___x_1504_;
}
pub unsafe fn l_Lean_instToExprUInt32___lam__0(
    mut v_a_1505_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1506_ = lean_uint32_to_nat(v_a_1505_);
    v_r_1507_ = l_Lean_mkRawNatLit(v___x_1506_);
    v___x_1508_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1509_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt32___lam__0___closed__2,
    );
    v___x_1510_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___lam__0___closed__4_once),
        _init_l_Lean_instToExprUInt32___lam__0___closed__4,
    );
    leanh::lean_inc_ref(v_r_1507_);
    v___x_1511_ = l_Lean_Expr_app___override(v___x_1510_, v_r_1507_);
    v___x_1512_ = l_Lean_mkApp3(v___x_1508_, v___x_1509_, v_r_1507_, v___x_1511_);
    return v___x_1512_;
}
pub unsafe fn l_Lean_instToExprUInt32___lam__0___boxed(
    mut v_a_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1514_: u32 = 0;
    let mut v_res_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1514_ = leanh::lean_unbox_uint32(v_a_1513_);
    leanh::lean_dec(v_a_1513_);
    v_res_1515_ = l_Lean_instToExprUInt32___lam__0(v_a_boxed_1514_);
    return v_res_1515_;
}
pub unsafe fn _init_l_Lean_instToExprUInt32___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt32___lam__0___closed__2,
    );
    v___f_1518_ = l_Lean_instToExprUInt32___closed__0;
    v___x_1519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1519_, 0, v___f_1518_);
    leanh::lean_ctor_set(v___x_1519_, 1, v___x_1517_);
    return v___x_1519_;
}
pub unsafe fn _init_l_Lean_instToExprUInt32() -> *mut leanh::LeanObject {
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1520_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt32___closed__1_once),
        _init_l_Lean_instToExprUInt32___closed__1,
    );
    return v___x_1520_;
}
pub unsafe fn _init_l_Lean_instToExprUInt64___lam__0___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = leanh::lean_box(0);
    v___x_1525_ = l_Lean_instToExprUInt64___lam__0___closed__1;
    v___x_1526_ = l_Lean_mkConst(v___x_1525_, v___x_1524_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Lean_instToExprUInt64___lam__0___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = leanh::lean_box(0);
    v___x_1531_ = l_Lean_instToExprUInt64___lam__0___closed__3;
    v___x_1532_ = l_Lean_Expr_const___override(v___x_1531_, v___x_1530_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_instToExprUInt64___lam__0(
    mut v_a_1533_: u64,
) -> *mut leanh::LeanObject {
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = lean_uint64_to_nat(v_a_1533_);
    v_r_1535_ = l_Lean_mkRawNatLit(v___x_1534_);
    v___x_1536_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1537_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt64___lam__0___closed__2,
    );
    v___x_1538_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___lam__0___closed__4_once),
        _init_l_Lean_instToExprUInt64___lam__0___closed__4,
    );
    leanh::lean_inc_ref(v_r_1535_);
    v___x_1539_ = l_Lean_Expr_app___override(v___x_1538_, v_r_1535_);
    v___x_1540_ = l_Lean_mkApp3(v___x_1536_, v___x_1537_, v_r_1535_, v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lean_instToExprUInt64___lam__0___boxed(
    mut v_a_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1542_: u64 = 0;
    let mut v_res_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1542_ = leanh::lean_unbox_uint64(v_a_1541_);
    leanh::lean_dec_ref(v_a_1541_);
    v_res_1543_ = l_Lean_instToExprUInt64___lam__0(v_a_boxed_1542_);
    return v_res_1543_;
}
pub unsafe fn _init_l_Lean_instToExprUInt64___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1545_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___lam__0___closed__2_once),
        _init_l_Lean_instToExprUInt64___lam__0___closed__2,
    );
    v___f_1546_ = l_Lean_instToExprUInt64___closed__0;
    v___x_1547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1547_, 0, v___f_1546_);
    leanh::lean_ctor_set(v___x_1547_, 1, v___x_1545_);
    return v___x_1547_;
}
pub unsafe fn _init_l_Lean_instToExprUInt64() -> *mut leanh::LeanObject {
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprUInt64___closed__1_once),
        _init_l_Lean_instToExprUInt64___closed__1,
    );
    return v___x_1548_;
}
pub unsafe fn _init_l_Lean_instToExprUSize___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = leanh::lean_box(0);
    v___x_1553_ = l_Lean_instToExprUSize___lam__0___closed__1;
    v___x_1554_ = l_Lean_mkConst(v___x_1553_, v___x_1552_);
    return v___x_1554_;
}
pub unsafe fn _init_l_Lean_instToExprUSize___lam__0___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = leanh::lean_box(0);
    v___x_1559_ = l_Lean_instToExprUSize___lam__0___closed__3;
    v___x_1560_ = l_Lean_Expr_const___override(v___x_1559_, v___x_1558_);
    return v___x_1560_;
}
pub unsafe fn l_Lean_instToExprUSize___lam__0(
    mut v_a_1561_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ = lean_usize_to_nat(v_a_1561_);
    v_r_1563_ = l_Lean_mkRawNatLit(v___x_1562_);
    v___x_1564_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1565_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___lam__0___closed__2_once),
        _init_l_Lean_instToExprUSize___lam__0___closed__2,
    );
    v___x_1566_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___lam__0___closed__4_once),
        _init_l_Lean_instToExprUSize___lam__0___closed__4,
    );
    leanh::lean_inc_ref(v_r_1563_);
    v___x_1567_ = l_Lean_Expr_app___override(v___x_1566_, v_r_1563_);
    v___x_1568_ = l_Lean_mkApp3(v___x_1564_, v___x_1565_, v_r_1563_, v___x_1567_);
    return v___x_1568_;
}
pub unsafe fn l_Lean_instToExprUSize___lam__0___boxed(
    mut v_a_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1570_: usize = 0;
    let mut v_res_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1570_ = leanh::lean_unbox_usize(v_a_1569_);
    leanh::lean_dec(v_a_1569_);
    v_res_1571_ = l_Lean_instToExprUSize___lam__0(v_a_boxed_1570_);
    return v_res_1571_;
}
pub unsafe fn _init_l_Lean_instToExprUSize___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___lam__0___closed__2_once),
        _init_l_Lean_instToExprUSize___lam__0___closed__2,
    );
    v___f_1574_ = l_Lean_instToExprUSize___closed__0;
    v___x_1575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1575_, 0, v___f_1574_);
    leanh::lean_ctor_set(v___x_1575_, 1, v___x_1573_);
    return v___x_1575_;
}
pub unsafe fn _init_l_Lean_instToExprUSize() -> *mut leanh::LeanObject {
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1576_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprUSize___closed__1_once),
        _init_l_Lean_instToExprUSize___closed__1,
    );
    return v___x_1576_;
}
pub unsafe fn _init_l_Lean_instToExprInt8_mkNat___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = leanh::lean_box(0);
    v___x_1581_ = l_Lean_instToExprInt8_mkNat___closed__1;
    v___x_1582_ = l_Lean_Expr_const___override(v___x_1581_, v___x_1580_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_instToExprInt8_mkNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = leanh::lean_box(0);
    v___x_1587_ = l_Lean_instToExprInt8_mkNat___closed__3;
    v___x_1588_ = l_Lean_Expr_const___override(v___x_1587_, v___x_1586_);
    return v___x_1588_;
}
pub unsafe fn l_Lean_instToExprInt8_mkNat(
    mut v_n_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1590_ = l_Lean_mkRawNatLit(v_n_1589_);
    v___x_1591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1592_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8_mkNat___closed__2_once),
        _init_l_Lean_instToExprInt8_mkNat___closed__2,
    );
    v___x_1593_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt8_mkNat___closed__4,
    );
    leanh::lean_inc_ref(v_r_1590_);
    v___x_1594_ = l_Lean_Expr_app___override(v___x_1593_, v_r_1590_);
    v___x_1595_ = l_Lean_mkApp3(v___x_1591_, v___x_1592_, v_r_1590_, v___x_1594_);
    return v___x_1595_;
}
pub unsafe fn _init_l_Lean_instToExprInt8___lam__0___closed__0() -> u8 {
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: u8 = 0;
    v___x_1596_ = leanh::lean_unsigned_to_nat(0);
    v___x_1597_ = lean_int8_of_nat(v___x_1596_);
    return v___x_1597_;
}
pub unsafe fn _init_l_Lean_instToExprInt8___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = leanh::lean_box(0);
    v___x_1602_ = l_Lean_instToExprInt8___lam__0___closed__1;
    v___x_1603_ = l_Lean_Expr_const___override(v___x_1602_, v___x_1601_);
    return v___x_1603_;
}
pub unsafe fn l_Lean_instToExprInt8___lam__0(mut v_i_1604_: u8) -> *mut leanh::LeanObject {
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: u8 = 0;
    v___x_1605_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8___lam__0___closed__0_once),
        _init_l_Lean_instToExprInt8___lam__0___closed__0,
    );
    v___x_1606_ = lean_int8_dec_le(v___x_1605_, v_i_1604_);
    if v___x_1606_ == 0 {
        let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1607_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4_once),
            _init_l_Lean_instToExprInt___lam__0___closed__4,
        );
        v___x_1608_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt8_mkNat___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt8_mkNat___closed__2_once),
            _init_l_Lean_instToExprInt8_mkNat___closed__2,
        );
        v___x_1609_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt8___lam__0___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt8___lam__0___closed__2_once),
            _init_l_Lean_instToExprInt8___lam__0___closed__2,
        );
        v___x_1610_ = lean_int8_to_int(v_i_1604_);
        v___x_1611_ = lean_int_neg(v___x_1610_);
        v___x_1612_ = l_Int_toNat(v___x_1611_);
        leanh::lean_dec(v___x_1611_);
        v___x_1613_ = l_Lean_instToExprInt8_mkNat(v___x_1612_);
        v___x_1614_ = l_Lean_mkApp3(v___x_1607_, v___x_1608_, v___x_1609_, v___x_1613_);
        return v___x_1614_;
    } else {
        let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1615_ = lean_int8_to_int(v_i_1604_);
        v___x_1616_ = l_Int_toNat(v___x_1615_);
        v___x_1617_ = l_Lean_instToExprInt8_mkNat(v___x_1616_);
        return v___x_1617_;
    }
}
pub unsafe fn l_Lean_instToExprInt8___lam__0___boxed(
    mut v_i_1618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1619_: u8 = 0;
    let mut v_res_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1619_ = (leanh::lean_unbox(v_i_1618_) as u8);
    v_res_1620_ = l_Lean_instToExprInt8___lam__0(v_i_boxed_1619_);
    return v_res_1620_;
}
pub unsafe fn _init_l_Lean_instToExprInt8___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = leanh::lean_box(0);
    v___x_1623_ = l_Lean_instToExprInt8_mkNat___closed__1;
    v___x_1624_ = l_Lean_mkConst(v___x_1623_, v___x_1622_);
    return v___x_1624_;
}
pub unsafe fn _init_l_Lean_instToExprInt8___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8___closed__1_once),
        _init_l_Lean_instToExprInt8___closed__1,
    );
    v___f_1626_ = l_Lean_instToExprInt8___closed__0;
    v___x_1627_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1627_, 0, v___f_1626_);
    leanh::lean_ctor_set(v___x_1627_, 1, v___x_1625_);
    return v___x_1627_;
}
pub unsafe fn _init_l_Lean_instToExprInt8() -> *mut leanh::LeanObject {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt8___closed__2_once),
        _init_l_Lean_instToExprInt8___closed__2,
    );
    return v___x_1628_;
}
pub unsafe fn _init_l_Lean_instToExprInt16_mkNat___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1632_ = leanh::lean_box(0);
    v___x_1633_ = l_Lean_instToExprInt16_mkNat___closed__1;
    v___x_1634_ = l_Lean_Expr_const___override(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Lean_instToExprInt16_mkNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = leanh::lean_box(0);
    v___x_1639_ = l_Lean_instToExprInt16_mkNat___closed__3;
    v___x_1640_ = l_Lean_Expr_const___override(v___x_1639_, v___x_1638_);
    return v___x_1640_;
}
pub unsafe fn l_Lean_instToExprInt16_mkNat(
    mut v_n_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1642_ = l_Lean_mkRawNatLit(v_n_1641_);
    v___x_1643_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1644_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16_mkNat___closed__2_once),
        _init_l_Lean_instToExprInt16_mkNat___closed__2,
    );
    v___x_1645_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt16_mkNat___closed__4,
    );
    leanh::lean_inc_ref(v_r_1642_);
    v___x_1646_ = l_Lean_Expr_app___override(v___x_1645_, v_r_1642_);
    v___x_1647_ = l_Lean_mkApp3(v___x_1643_, v___x_1644_, v_r_1642_, v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn _init_l_Lean_instToExprInt16___lam__0___closed__0() -> u16 {
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: u16 = 0;
    v___x_1648_ = leanh::lean_unsigned_to_nat(0);
    v___x_1649_ = lean_int16_of_nat(v___x_1648_);
    return v___x_1649_;
}
pub unsafe fn _init_l_Lean_instToExprInt16___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = leanh::lean_box(0);
    v___x_1654_ = l_Lean_instToExprInt16___lam__0___closed__1;
    v___x_1655_ = l_Lean_Expr_const___override(v___x_1654_, v___x_1653_);
    return v___x_1655_;
}
pub unsafe fn l_Lean_instToExprInt16___lam__0(mut v_i_1656_: u16) -> *mut leanh::LeanObject {
    let mut v___x_1657_: u16 = 0;
    let mut v___x_1658_: u8 = 0;
    v___x_1657_ = leanh::lean_uint16_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16___lam__0___closed__0_once),
        _init_l_Lean_instToExprInt16___lam__0___closed__0,
    );
    v___x_1658_ = lean_int16_dec_le(v___x_1657_, v_i_1656_);
    if v___x_1658_ == 0 {
        let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1659_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4_once),
            _init_l_Lean_instToExprInt___lam__0___closed__4,
        );
        v___x_1660_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt16_mkNat___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt16_mkNat___closed__2_once),
            _init_l_Lean_instToExprInt16_mkNat___closed__2,
        );
        v___x_1661_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt16___lam__0___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt16___lam__0___closed__2_once),
            _init_l_Lean_instToExprInt16___lam__0___closed__2,
        );
        v___x_1662_ = lean_int16_to_int(v_i_1656_);
        v___x_1663_ = lean_int_neg(v___x_1662_);
        v___x_1664_ = l_Int_toNat(v___x_1663_);
        leanh::lean_dec(v___x_1663_);
        v___x_1665_ = l_Lean_instToExprInt16_mkNat(v___x_1664_);
        v___x_1666_ = l_Lean_mkApp3(v___x_1659_, v___x_1660_, v___x_1661_, v___x_1665_);
        return v___x_1666_;
    } else {
        let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1667_ = lean_int16_to_int(v_i_1656_);
        v___x_1668_ = l_Int_toNat(v___x_1667_);
        v___x_1669_ = l_Lean_instToExprInt16_mkNat(v___x_1668_);
        return v___x_1669_;
    }
}
pub unsafe fn l_Lean_instToExprInt16___lam__0___boxed(
    mut v_i_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1671_: u16 = 0;
    let mut v_res_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1671_ = (leanh::lean_unbox(v_i_1670_) as u16);
    v_res_1672_ = l_Lean_instToExprInt16___lam__0(v_i_boxed_1671_);
    return v_res_1672_;
}
pub unsafe fn _init_l_Lean_instToExprInt16___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = leanh::lean_box(0);
    v___x_1675_ = l_Lean_instToExprInt16_mkNat___closed__1;
    v___x_1676_ = l_Lean_mkConst(v___x_1675_, v___x_1674_);
    return v___x_1676_;
}
pub unsafe fn _init_l_Lean_instToExprInt16___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1677_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16___closed__1_once),
        _init_l_Lean_instToExprInt16___closed__1,
    );
    v___f_1678_ = l_Lean_instToExprInt16___closed__0;
    v___x_1679_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1679_, 0, v___f_1678_);
    leanh::lean_ctor_set(v___x_1679_, 1, v___x_1677_);
    return v___x_1679_;
}
pub unsafe fn _init_l_Lean_instToExprInt16() -> *mut leanh::LeanObject {
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt16___closed__2_once),
        _init_l_Lean_instToExprInt16___closed__2,
    );
    return v___x_1680_;
}
pub unsafe fn _init_l_Lean_instToExprInt32_mkNat___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1684_ = leanh::lean_box(0);
    v___x_1685_ = l_Lean_instToExprInt32_mkNat___closed__1;
    v___x_1686_ = l_Lean_Expr_const___override(v___x_1685_, v___x_1684_);
    return v___x_1686_;
}
pub unsafe fn _init_l_Lean_instToExprInt32_mkNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = leanh::lean_box(0);
    v___x_1691_ = l_Lean_instToExprInt32_mkNat___closed__3;
    v___x_1692_ = l_Lean_Expr_const___override(v___x_1691_, v___x_1690_);
    return v___x_1692_;
}
pub unsafe fn l_Lean_instToExprInt32_mkNat(
    mut v_n_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1694_ = l_Lean_mkRawNatLit(v_n_1693_);
    v___x_1695_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1696_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32_mkNat___closed__2_once),
        _init_l_Lean_instToExprInt32_mkNat___closed__2,
    );
    v___x_1697_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt32_mkNat___closed__4,
    );
    leanh::lean_inc_ref(v_r_1694_);
    v___x_1698_ = l_Lean_Expr_app___override(v___x_1697_, v_r_1694_);
    v___x_1699_ = l_Lean_mkApp3(v___x_1695_, v___x_1696_, v_r_1694_, v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn _init_l_Lean_instToExprInt32___lam__0___closed__0() -> u32 {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u32 = 0;
    v___x_1700_ = leanh::lean_unsigned_to_nat(0);
    v___x_1701_ = lean_int32_of_nat(v___x_1700_);
    return v___x_1701_;
}
pub unsafe fn _init_l_Lean_instToExprInt32___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = leanh::lean_box(0);
    v___x_1706_ = l_Lean_instToExprInt32___lam__0___closed__1;
    v___x_1707_ = l_Lean_Expr_const___override(v___x_1706_, v___x_1705_);
    return v___x_1707_;
}
pub unsafe fn l_Lean_instToExprInt32___lam__0(mut v_i_1708_: u32) -> *mut leanh::LeanObject {
    let mut v___x_1709_: u32 = 0;
    let mut v___x_1710_: u8 = 0;
    v___x_1709_ = leanh::lean_uint32_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32___lam__0___closed__0_once),
        _init_l_Lean_instToExprInt32___lam__0___closed__0,
    );
    v___x_1710_ = lean_int32_dec_le(v___x_1709_, v_i_1708_);
    if v___x_1710_ == 0 {
        let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1711_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4_once),
            _init_l_Lean_instToExprInt___lam__0___closed__4,
        );
        v___x_1712_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt32_mkNat___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt32_mkNat___closed__2_once),
            _init_l_Lean_instToExprInt32_mkNat___closed__2,
        );
        v___x_1713_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt32___lam__0___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt32___lam__0___closed__2_once),
            _init_l_Lean_instToExprInt32___lam__0___closed__2,
        );
        v___x_1714_ = lean_int32_to_int(v_i_1708_);
        v___x_1715_ = lean_int_neg(v___x_1714_);
        leanh::lean_dec(v___x_1714_);
        v___x_1716_ = l_Int_toNat(v___x_1715_);
        leanh::lean_dec(v___x_1715_);
        v___x_1717_ = l_Lean_instToExprInt32_mkNat(v___x_1716_);
        v___x_1718_ = l_Lean_mkApp3(v___x_1711_, v___x_1712_, v___x_1713_, v___x_1717_);
        return v___x_1718_;
    } else {
        let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1719_ = lean_int32_to_int(v_i_1708_);
        v___x_1720_ = l_Int_toNat(v___x_1719_);
        leanh::lean_dec(v___x_1719_);
        v___x_1721_ = l_Lean_instToExprInt32_mkNat(v___x_1720_);
        return v___x_1721_;
    }
}
pub unsafe fn l_Lean_instToExprInt32___lam__0___boxed(
    mut v_i_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1723_: u32 = 0;
    let mut v_res_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1723_ = leanh::lean_unbox_uint32(v_i_1722_);
    leanh::lean_dec(v_i_1722_);
    v_res_1724_ = l_Lean_instToExprInt32___lam__0(v_i_boxed_1723_);
    return v_res_1724_;
}
pub unsafe fn _init_l_Lean_instToExprInt32___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1726_ = leanh::lean_box(0);
    v___x_1727_ = l_Lean_instToExprInt32_mkNat___closed__1;
    v___x_1728_ = l_Lean_mkConst(v___x_1727_, v___x_1726_);
    return v___x_1728_;
}
pub unsafe fn _init_l_Lean_instToExprInt32___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32___closed__1_once),
        _init_l_Lean_instToExprInt32___closed__1,
    );
    v___f_1730_ = l_Lean_instToExprInt32___closed__0;
    v___x_1731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1731_, 0, v___f_1730_);
    leanh::lean_ctor_set(v___x_1731_, 1, v___x_1729_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Lean_instToExprInt32() -> *mut leanh::LeanObject {
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt32___closed__2_once),
        _init_l_Lean_instToExprInt32___closed__2,
    );
    return v___x_1732_;
}
pub unsafe fn _init_l_Lean_instToExprInt64_mkNat___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = leanh::lean_box(0);
    v___x_1737_ = l_Lean_instToExprInt64_mkNat___closed__1;
    v___x_1738_ = l_Lean_Expr_const___override(v___x_1737_, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l_Lean_instToExprInt64_mkNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = leanh::lean_box(0);
    v___x_1743_ = l_Lean_instToExprInt64_mkNat___closed__3;
    v___x_1744_ = l_Lean_Expr_const___override(v___x_1743_, v___x_1742_);
    return v___x_1744_;
}
pub unsafe fn l_Lean_instToExprInt64_mkNat(
    mut v_n_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1746_ = l_Lean_mkRawNatLit(v_n_1745_);
    v___x_1747_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1748_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64_mkNat___closed__2_once),
        _init_l_Lean_instToExprInt64_mkNat___closed__2,
    );
    v___x_1749_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64_mkNat___closed__4_once),
        _init_l_Lean_instToExprInt64_mkNat___closed__4,
    );
    leanh::lean_inc_ref(v_r_1746_);
    v___x_1750_ = l_Lean_Expr_app___override(v___x_1749_, v_r_1746_);
    v___x_1751_ = l_Lean_mkApp3(v___x_1747_, v___x_1748_, v_r_1746_, v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn _init_l_Lean_instToExprInt64___lam__0___closed__0() -> u64 {
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u64 = 0;
    v___x_1752_ = leanh::lean_unsigned_to_nat(0);
    v___x_1753_ = lean_int64_of_nat(v___x_1752_);
    return v___x_1753_;
}
pub unsafe fn _init_l_Lean_instToExprInt64___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = leanh::lean_box(0);
    v___x_1758_ = l_Lean_instToExprInt64___lam__0___closed__1;
    v___x_1759_ = l_Lean_Expr_const___override(v___x_1758_, v___x_1757_);
    return v___x_1759_;
}
pub unsafe fn l_Lean_instToExprInt64___lam__0(mut v_i_1760_: u64) -> *mut leanh::LeanObject {
    let mut v___x_1761_: u64 = 0;
    let mut v___x_1762_: u8 = 0;
    v___x_1761_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64___lam__0___closed__0_once),
        _init_l_Lean_instToExprInt64___lam__0___closed__0,
    );
    v___x_1762_ = lean_int64_dec_le(v___x_1761_, v_i_1760_);
    if v___x_1762_ == 0 {
        let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1763_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4_once),
            _init_l_Lean_instToExprInt___lam__0___closed__4,
        );
        v___x_1764_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt64_mkNat___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt64_mkNat___closed__2_once),
            _init_l_Lean_instToExprInt64_mkNat___closed__2,
        );
        v___x_1765_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt64___lam__0___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt64___lam__0___closed__2_once),
            _init_l_Lean_instToExprInt64___lam__0___closed__2,
        );
        v___x_1766_ = lean_int64_to_int_sint(v_i_1760_);
        v___x_1767_ = lean_int_neg(v___x_1766_);
        leanh::lean_dec(v___x_1766_);
        v___x_1768_ = l_Int_toNat(v___x_1767_);
        leanh::lean_dec(v___x_1767_);
        v___x_1769_ = l_Lean_instToExprInt64_mkNat(v___x_1768_);
        v___x_1770_ = l_Lean_mkApp3(v___x_1763_, v___x_1764_, v___x_1765_, v___x_1769_);
        return v___x_1770_;
    } else {
        let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1771_ = lean_int64_to_int_sint(v_i_1760_);
        v___x_1772_ = l_Int_toNat(v___x_1771_);
        leanh::lean_dec(v___x_1771_);
        v___x_1773_ = l_Lean_instToExprInt64_mkNat(v___x_1772_);
        return v___x_1773_;
    }
}
pub unsafe fn l_Lean_instToExprInt64___lam__0___boxed(
    mut v_i_1774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1775_: u64 = 0;
    let mut v_res_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1775_ = leanh::lean_unbox_uint64(v_i_1774_);
    leanh::lean_dec_ref(v_i_1774_);
    v_res_1776_ = l_Lean_instToExprInt64___lam__0(v_i_boxed_1775_);
    return v_res_1776_;
}
pub unsafe fn _init_l_Lean_instToExprInt64___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = leanh::lean_box(0);
    v___x_1779_ = l_Lean_instToExprInt64_mkNat___closed__1;
    v___x_1780_ = l_Lean_mkConst(v___x_1779_, v___x_1778_);
    return v___x_1780_;
}
pub unsafe fn _init_l_Lean_instToExprInt64___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64___closed__1_once),
        _init_l_Lean_instToExprInt64___closed__1,
    );
    v___f_1782_ = l_Lean_instToExprInt64___closed__0;
    v___x_1783_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1783_, 0, v___f_1782_);
    leanh::lean_ctor_set(v___x_1783_, 1, v___x_1781_);
    return v___x_1783_;
}
pub unsafe fn _init_l_Lean_instToExprInt64() -> *mut leanh::LeanObject {
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt64___closed__2_once),
        _init_l_Lean_instToExprInt64___closed__2,
    );
    return v___x_1784_;
}
pub unsafe fn _init_l_Lean_instToExprISize_mkNat___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = leanh::lean_box(0);
    v___x_1789_ = l_Lean_instToExprISize_mkNat___closed__1;
    v___x_1790_ = l_Lean_Expr_const___override(v___x_1789_, v___x_1788_);
    return v___x_1790_;
}
pub unsafe fn _init_l_Lean_instToExprISize_mkNat___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1794_ = leanh::lean_box(0);
    v___x_1795_ = l_Lean_instToExprISize_mkNat___closed__3;
    v___x_1796_ = l_Lean_Expr_const___override(v___x_1795_, v___x_1794_);
    return v___x_1796_;
}
pub unsafe fn l_Lean_instToExprISize_mkNat(
    mut v_n_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_1798_ = l_Lean_mkRawNatLit(v_n_1797_);
    v___x_1799_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5),
        core::ptr::addr_of_mut!(l_Lean_instToExprInt_mkNat___closed__5_once),
        _init_l_Lean_instToExprInt_mkNat___closed__5,
    );
    v___x_1800_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprISize_mkNat___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprISize_mkNat___closed__2_once),
        _init_l_Lean_instToExprISize_mkNat___closed__2,
    );
    v___x_1801_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprISize_mkNat___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprISize_mkNat___closed__4_once),
        _init_l_Lean_instToExprISize_mkNat___closed__4,
    );
    leanh::lean_inc_ref(v_r_1798_);
    v___x_1802_ = l_Lean_Expr_app___override(v___x_1801_, v_r_1798_);
    v___x_1803_ = l_Lean_mkApp3(v___x_1799_, v___x_1800_, v_r_1798_, v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn _init_l_Lean_instToExprISize___lam__0___closed__0() -> usize {
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: usize = 0;
    v___x_1804_ = leanh::lean_unsigned_to_nat(0);
    v___x_1805_ = lean_isize_of_nat(v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn _init_l_Lean_instToExprISize___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = leanh::lean_box(0);
    v___x_1810_ = l_Lean_instToExprISize___lam__0___closed__1;
    v___x_1811_ = l_Lean_Expr_const___override(v___x_1810_, v___x_1809_);
    return v___x_1811_;
}
pub unsafe fn l_Lean_instToExprISize___lam__0(
    mut v_i_1812_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_1813_: usize = 0;
    let mut v___x_1814_: u8 = 0;
    v___x_1813_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprISize___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprISize___lam__0___closed__0_once),
        _init_l_Lean_instToExprISize___lam__0___closed__0,
    );
    v___x_1814_ = lean_isize_dec_le(v___x_1813_, v_i_1812_);
    if v___x_1814_ == 0 {
        let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1815_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprInt___lam__0___closed__4_once),
            _init_l_Lean_instToExprInt___lam__0___closed__4,
        );
        v___x_1816_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprISize_mkNat___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprISize_mkNat___closed__2_once),
            _init_l_Lean_instToExprISize_mkNat___closed__2,
        );
        v___x_1817_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprISize___lam__0___closed__2),
            core::ptr::addr_of_mut!(l_Lean_instToExprISize___lam__0___closed__2_once),
            _init_l_Lean_instToExprISize___lam__0___closed__2,
        );
        v___x_1818_ = lean_isize_to_int(v_i_1812_);
        v___x_1819_ = lean_int_neg(v___x_1818_);
        leanh::lean_dec(v___x_1818_);
        v___x_1820_ = l_Int_toNat(v___x_1819_);
        leanh::lean_dec(v___x_1819_);
        v___x_1821_ = l_Lean_instToExprISize_mkNat(v___x_1820_);
        v___x_1822_ = l_Lean_mkApp3(v___x_1815_, v___x_1816_, v___x_1817_, v___x_1821_);
        return v___x_1822_;
    } else {
        let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1823_ = lean_isize_to_int(v_i_1812_);
        v___x_1824_ = l_Int_toNat(v___x_1823_);
        leanh::lean_dec(v___x_1823_);
        v___x_1825_ = l_Lean_instToExprISize_mkNat(v___x_1824_);
        return v___x_1825_;
    }
}
pub unsafe fn l_Lean_instToExprISize___lam__0___boxed(
    mut v_i_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1827_: usize = 0;
    let mut v_res_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1827_ = leanh::lean_unbox_usize(v_i_1826_);
    leanh::lean_dec(v_i_1826_);
    v_res_1828_ = l_Lean_instToExprISize___lam__0(v_i_boxed_1827_);
    return v_res_1828_;
}
pub unsafe fn _init_l_Lean_instToExprISize___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = leanh::lean_box(0);
    v___x_1831_ = l_Lean_instToExprISize_mkNat___closed__1;
    v___x_1832_ = l_Lean_mkConst(v___x_1831_, v___x_1830_);
    return v___x_1832_;
}
pub unsafe fn _init_l_Lean_instToExprISize___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprISize___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprISize___closed__1_once),
        _init_l_Lean_instToExprISize___closed__1,
    );
    v___f_1834_ = l_Lean_instToExprISize___closed__0;
    v___x_1835_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1835_, 0, v___f_1834_);
    leanh::lean_ctor_set(v___x_1835_, 1, v___x_1833_);
    return v___x_1835_;
}
pub unsafe fn _init_l_Lean_instToExprISize() -> *mut leanh::LeanObject {
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprISize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprISize___closed__2_once),
        _init_l_Lean_instToExprISize___closed__2,
    );
    return v___x_1836_;
}
pub unsafe fn _init_l_Lean_instToExprBool___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = leanh::lean_box(0);
    v___x_1843_ = l_Lean_instToExprBool___lam__0___closed__2;
    v___x_1844_ = l_Lean_mkConst(v___x_1843_, v___x_1842_);
    return v___x_1844_;
}
pub unsafe fn _init_l_Lean_instToExprBool___lam__0___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = leanh::lean_box(0);
    v___x_1850_ = l_Lean_instToExprBool___lam__0___closed__5;
    v___x_1851_ = l_Lean_mkConst(v___x_1850_, v___x_1849_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_instToExprBool___lam__0(mut v_b_1852_: u8) -> *mut leanh::LeanObject {
    if v_b_1852_ == 0 {
        let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1853_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprBool___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Lean_instToExprBool___lam__0___closed__3_once),
            _init_l_Lean_instToExprBool___lam__0___closed__3,
        );
        return v___x_1853_;
    } else {
        let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1854_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprBool___lam__0___closed__6),
            core::ptr::addr_of_mut!(l_Lean_instToExprBool___lam__0___closed__6_once),
            _init_l_Lean_instToExprBool___lam__0___closed__6,
        );
        return v___x_1854_;
    }
}
pub unsafe fn l_Lean_instToExprBool___lam__0___boxed(
    mut v_b_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1856_: u8 = 0;
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1856_ = (leanh::lean_unbox(v_b_1855_) as u8);
    v_res_1857_ = l_Lean_instToExprBool___lam__0(v_b_boxed_1856_);
    return v_res_1857_;
}
pub unsafe fn _init_l_Lean_instToExprBool___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = leanh::lean_box(0);
    v___x_1862_ = l_Lean_instToExprBool___closed__1;
    v___x_1863_ = l_Lean_mkConst(v___x_1862_, v___x_1861_);
    return v___x_1863_;
}
pub unsafe fn _init_l_Lean_instToExprBool___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprBool___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprBool___closed__2_once),
        _init_l_Lean_instToExprBool___closed__2,
    );
    v___f_1865_ = l_Lean_instToExprBool___closed__0;
    v___x_1866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1866_, 0, v___f_1865_);
    leanh::lean_ctor_set(v___x_1866_, 1, v___x_1864_);
    return v___x_1866_;
}
pub unsafe fn _init_l_Lean_instToExprBool() -> *mut leanh::LeanObject {
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1867_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprBool___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprBool___closed__3_once),
        _init_l_Lean_instToExprBool___closed__3,
    );
    return v___x_1867_;
}
pub unsafe fn _init_l_Lean_instToExprChar___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1872_ = leanh::lean_box(0);
    v___x_1873_ = l_Lean_instToExprChar___lam__0___closed__1;
    v___x_1874_ = l_Lean_mkConst(v___x_1873_, v___x_1872_);
    return v___x_1874_;
}
pub unsafe fn l_Lean_instToExprChar___lam__0(mut v_c_1875_: u32) -> *mut leanh::LeanObject {
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprChar___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprChar___lam__0___closed__2_once),
        _init_l_Lean_instToExprChar___lam__0___closed__2,
    );
    v___x_1877_ = lean_uint32_to_nat(v_c_1875_);
    v___x_1878_ = l_Lean_mkRawNatLit(v___x_1877_);
    v___x_1879_ = l_Lean_Expr_app___override(v___x_1876_, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_instToExprChar___lam__0___boxed(
    mut v_c_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1881_: u32 = 0;
    let mut v_res_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1881_ = leanh::lean_unbox_uint32(v_c_1880_);
    leanh::lean_dec(v_c_1880_);
    v_res_1882_ = l_Lean_instToExprChar___lam__0(v_c_boxed_1881_);
    return v_res_1882_;
}
pub unsafe fn _init_l_Lean_instToExprChar___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1886_ = leanh::lean_box(0);
    v___x_1887_ = l_Lean_instToExprChar___closed__1;
    v___x_1888_ = l_Lean_mkConst(v___x_1887_, v___x_1886_);
    return v___x_1888_;
}
pub unsafe fn _init_l_Lean_instToExprChar___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprChar___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprChar___closed__2_once),
        _init_l_Lean_instToExprChar___closed__2,
    );
    v___f_1890_ = l_Lean_instToExprChar___closed__0;
    v___x_1891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1891_, 0, v___f_1890_);
    leanh::lean_ctor_set(v___x_1891_, 1, v___x_1889_);
    return v___x_1891_;
}
pub unsafe fn _init_l_Lean_instToExprChar() -> *mut leanh::LeanObject {
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprChar___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprChar___closed__3_once),
        _init_l_Lean_instToExprChar___closed__3,
    );
    return v___x_1892_;
}
pub unsafe fn _init_l_Lean_instToExprString___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = leanh::lean_box(0);
    v___x_1898_ = l_Lean_instToExprString___closed__2;
    v___x_1899_ = l_Lean_mkConst(v___x_1898_, v___x_1897_);
    return v___x_1899_;
}
pub unsafe fn _init_l_Lean_instToExprString___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__3_once),
        _init_l_Lean_instToExprString___closed__3,
    );
    v___x_1901_ = l_Lean_instToExprString___closed__0;
    v___x_1902_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1902_, 0, v___x_1901_);
    leanh::lean_ctor_set(v___x_1902_, 1, v___x_1900_);
    return v___x_1902_;
}
pub unsafe fn _init_l_Lean_instToExprString() -> *mut leanh::LeanObject {
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1903_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__4_once),
        _init_l_Lean_instToExprString___closed__4,
    );
    return v___x_1903_;
}
pub unsafe fn _init_l_Lean_instToExprUnit___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1909_ = leanh::lean_box(0);
    v___x_1910_ = l_Lean_instToExprUnit___lam__0___closed__2;
    v___x_1911_ = l_Lean_mkConst(v___x_1910_, v___x_1909_);
    return v___x_1911_;
}
pub unsafe fn l_Lean_instToExprUnit___lam__0(
    mut v_x_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUnit___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprUnit___lam__0___closed__3_once),
        _init_l_Lean_instToExprUnit___lam__0___closed__3,
    );
    return v___x_1913_;
}
pub unsafe fn _init_l_Lean_instToExprUnit___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = leanh::lean_box(0);
    v___x_1918_ = l_Lean_instToExprUnit___closed__1;
    v___x_1919_ = l_Lean_mkConst(v___x_1918_, v___x_1917_);
    return v___x_1919_;
}
pub unsafe fn _init_l_Lean_instToExprUnit___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUnit___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprUnit___closed__2_once),
        _init_l_Lean_instToExprUnit___closed__2,
    );
    v___f_1921_ = l_Lean_instToExprUnit___closed__0;
    v___x_1922_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1922_, 0, v___f_1921_);
    leanh::lean_ctor_set(v___x_1922_, 1, v___x_1920_);
    return v___x_1922_;
}
pub unsafe fn _init_l_Lean_instToExprUnit() -> *mut leanh::LeanObject {
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprUnit___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprUnit___closed__3_once),
        _init_l_Lean_instToExprUnit___closed__3,
    );
    return v___x_1923_;
}
pub unsafe fn _init_l_Lean_instToExprFilePath___lam__0___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = leanh::lean_box(0);
    v___x_1932_ = l_Lean_instToExprFilePath___lam__0___closed__3;
    v___x_1933_ = l_Lean_mkConst(v___x_1932_, v___x_1931_);
    return v___x_1933_;
}
pub unsafe fn l_Lean_instToExprFilePath___lam__0(
    mut v_p_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFilePath___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_instToExprFilePath___lam__0___closed__4_once),
        _init_l_Lean_instToExprFilePath___lam__0___closed__4,
    );
    v___x_1936_ = l_Lean_mkStrLit(v_p_1934_);
    v___x_1937_ = l_Lean_Expr_app___override(v___x_1935_, v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn _init_l_Lean_instToExprFilePath___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = leanh::lean_box(0);
    v___x_1943_ = l_Lean_instToExprFilePath___closed__1;
    v___x_1944_ = l_Lean_mkConst(v___x_1943_, v___x_1942_);
    return v___x_1944_;
}
pub unsafe fn _init_l_Lean_instToExprFilePath___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFilePath___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprFilePath___closed__2_once),
        _init_l_Lean_instToExprFilePath___closed__2,
    );
    v___f_1946_ = l_Lean_instToExprFilePath___closed__0;
    v___x_1947_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1947_, 0, v___f_1946_);
    leanh::lean_ctor_set(v___x_1947_, 1, v___x_1945_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lean_instToExprFilePath() -> *mut leanh::LeanObject {
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFilePath___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprFilePath___closed__3_once),
        _init_l_Lean_instToExprFilePath___closed__3,
    );
    return v___x_1948_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(
    mut v_n_1949_: *mut leanh::LeanObject,
    mut v_sz_1950_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v_pre_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_n_1949_) {
                0 => {
                    v___x_1951_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1952_ = lean_nat_dec_lt(v___x_1951_, v_sz_1950_);
                    if v___x_1952_ == 0 {
                        leanh::lean_dec(v_sz_1950_);
                        return v___x_1952_;
                    } else {
                        v___x_1953_ = leanh::lean_unsigned_to_nat(8);
                        v___x_1954_ = lean_nat_dec_le(v_sz_1950_, v___x_1953_);
                        leanh::lean_dec(v_sz_1950_);
                        return v___x_1954_;
                    }
                }
                1 => {
                    v_pre_1955_ = leanh::lean_ctor_get(v_n_1949_, 0);
                    v___x_1956_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1957_ = lean_nat_add(v_sz_1950_, v___x_1956_);
                    leanh::lean_dec(v_sz_1950_);
                    v_n_1949_ = v_pre_1955_;
                    v_sz_1950_ = v___x_1957_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec(v_sz_1950_);
                    v___x_1959_ = 0;
                    return v___x_1959_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(
    mut v_n_1960_: *mut leanh::LeanObject,
    mut v_sz_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1962_: u8 = 0;
    let mut v_r_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1962_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(v_n_1960_, v_sz_1961_);
    leanh::lean_dec(v_n_1960_);
    v_r_1963_ = leanh::lean_box((v_res_1962_) as usize);
    return v_r_1963_;
}
pub unsafe fn l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(
    mut v_msg_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Lean_instInhabitedExpr;
    v___x_1966_ = lean_panic_fn_borrowed(v___x_1965_, v_msg_1964_);
    return v___x_1966_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1976_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6;
    v___x_1977_ = leanh::lean_unsigned_to_nat(11);
    v___x_1978_ = leanh::lean_unsigned_to_nat(221);
    v___x_1979_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5;
    v___x_1980_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4;
    v___x_1981_ = l_mkPanicMessageWithDecl(
        v___x_1980_,
        v___x_1979_,
        v___x_1978_,
        v___x_1977_,
        v___x_1976_,
    );
    return v___x_1981_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(
    mut v_n_1982_: *mut leanh::LeanObject,
    mut v_sz_1983_: *mut leanh::LeanObject,
    mut v_args_1984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match leanh::lean_obj_tag(v_n_1982_) {
                    0 => {
                        v___x_1985_ =
                            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2;
                        v___x_1986_ =
                            l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3;
                        v___x_1987_ = l_Nat_reprFast(v_sz_1983_);
                        v___x_1988_ = lean_string_append(v___x_1986_, v___x_1987_);
                        leanh::lean_dec_ref(v___x_1987_);
                        v___x_1989_ = l_Lean_Name_str___override(v___x_1985_, v___x_1988_);
                        v___x_1990_ = leanh::lean_box(0);
                        v___x_1991_ = l_Lean_mkConst(v___x_1989_, v___x_1990_);
                        v___x_1992_ = l_Array_reverse___redArg(v_args_1984_);
                        v___x_1993_ = l_Lean_mkAppN(v___x_1991_, v___x_1992_);
                        leanh::lean_dec_ref(v___x_1992_);
                        return v___x_1993_;
                    }
                    1 => {
                        v_pre_1994_ = leanh::lean_ctor_get(v_n_1982_, 0);
                        leanh::lean_inc(v_pre_1994_);
                        v_str_1995_ = leanh::lean_ctor_get(v_n_1982_, 1);
                        leanh::lean_inc_ref(v_str_1995_);
                        leanh::lean_dec_ref_known(v_n_1982_, 2);
                        v___x_1996_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1997_ = lean_nat_add(v_sz_1983_, v___x_1996_);
                        leanh::lean_dec(v_sz_1983_);
                        v___x_1998_ = l_Lean_mkStrLit(v_str_1995_);
                        v___x_1999_ = lean_array_push(v_args_1984_, v___x_1998_);
                        v_n_1982_ = v_pre_1994_;
                        v_sz_1983_ = v___x_1997_;
                        v_args_1984_ = v___x_1999_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref(v_args_1984_);
                        leanh::lean_dec(v_sz_1983_);
                        leanh::lean_dec(v_n_1982_);
                        v___x_2001_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7_once), _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7);
                        v___x_2002_ = l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(v___x_2001_);
                        return v___x_2002_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ = leanh::lean_box(0);
    v___x_2009_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1;
    v___x_2010_ = l_Lean_mkConst(v___x_2009_, v___x_2008_);
    return v___x_2010_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = leanh::lean_box(0);
    v___x_2017_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4;
    v___x_2018_ = l_Lean_mkConst(v___x_2017_, v___x_2016_);
    return v___x_2018_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2024_ = leanh::lean_box(0);
    v___x_2025_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7;
    v___x_2026_ = l_Lean_mkConst(v___x_2025_, v___x_2024_);
    return v___x_2026_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(
    mut v_a_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_a_2027_) {
        0 => {
            let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2028_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2_once
                ),
                _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2,
            );
            return v___x_2028_;
        }
        1 => {
            let mut v_pre_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_2029_ = leanh::lean_ctor_get(v_a_2027_, 0);
            leanh::lean_inc(v_pre_2029_);
            v_str_2030_ = leanh::lean_ctor_get(v_a_2027_, 1);
            leanh::lean_inc_ref(v_str_2030_);
            leanh::lean_dec_ref_known(v_a_2027_, 2);
            v___x_2031_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5_once
                ),
                _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5,
            );
            v___x_2032_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_pre_2029_);
            v___x_2033_ = l_Lean_mkStrLit(v_str_2030_);
            v___x_2034_ = l_Lean_mkAppB(v___x_2031_, v___x_2032_, v___x_2033_);
            return v___x_2034_;
        }
        _ => {
            let mut v_pre_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_2035_ = leanh::lean_ctor_get(v_a_2027_, 0);
            leanh::lean_inc(v_pre_2035_);
            v_i_2036_ = leanh::lean_ctor_get(v_a_2027_, 1);
            leanh::lean_inc(v_i_2036_);
            leanh::lean_dec_ref_known(v_a_2027_, 2);
            v___x_2037_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8_once
                ),
                _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8,
            );
            v___x_2038_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_pre_2035_);
            v___x_2039_ = l_Lean_mkNatLit(v_i_2036_);
            v___x_2040_ = l_Lean_mkAppB(v___x_2037_, v___x_2038_, v___x_2039_);
            return v___x_2040_;
        }
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_Name_toExprAux(
    mut v_n_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    v___x_2044_ = leanh::lean_unsigned_to_nat(0);
    v___x_2045_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(v_n_2043_, v___x_2044_);
    if v___x_2045_ == 0 {
        let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2046_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_n_2043_);
        return v___x_2046_;
    } else {
        let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2047_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0;
        v___x_2048_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(
            v_n_2043_,
            v___x_2044_,
            v___x_2047_,
        );
        return v___x_2048_;
    }
}
pub unsafe fn l_Lean_instToExprName___private__1(
    mut v_n_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_n_2049_);
    return v___x_2050_;
}
pub unsafe fn _init_l_Lean_instToExprName___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = leanh::lean_box(0);
    v___x_2053_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2;
    v___x_2054_ = l_Lean_mkConst(v___x_2053_, v___x_2052_);
    return v___x_2054_;
}
pub unsafe fn _init_l_Lean_instToExprName___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprName___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instToExprName___closed__1_once),
        _init_l_Lean_instToExprName___closed__1,
    );
    v___x_2056_ = l_Lean_instToExprName___closed__0;
    v___x_2057_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2057_, 0, v___x_2056_);
    leanh::lean_ctor_set(v___x_2057_, 1, v___x_2055_);
    return v___x_2057_;
}
pub unsafe fn _init_l_Lean_instToExprName() -> *mut leanh::LeanObject {
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprName___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprName___closed__2_once),
        _init_l_Lean_instToExprName___closed__2,
    );
    return v___x_2058_;
}
pub unsafe fn l_Lean_instToExprOptionOfToLevel___redArg___lam__0(
    mut v_inst_2068_: *mut leanh::LeanObject,
    mut v_toTypeExpr_2069_: *mut leanh::LeanObject,
    mut v_toExpr_2070_: *mut leanh::LeanObject,
    mut v_o_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_o_2071_) == 0 {
        let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toExpr_2070_);
        v___x_2072_ = l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2;
        v___x_2073_ = leanh::lean_box(0);
        v___x_2074_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2074_, 0, v_inst_2068_);
        leanh::lean_ctor_set(v___x_2074_, 1, v___x_2073_);
        v___x_2075_ = l_Lean_mkConst(v___x_2072_, v___x_2074_);
        v___x_2076_ = l_Lean_Expr_app___override(v___x_2075_, v_toTypeExpr_2069_);
        return v___x_2076_;
    } else {
        let mut v_val_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2077_ = leanh::lean_ctor_get(v_o_2071_, 0);
        leanh::lean_inc(v_val_2077_);
        leanh::lean_dec_ref_known(v_o_2071_, 1);
        v___x_2078_ = l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4;
        v___x_2079_ = leanh::lean_box(0);
        v___x_2080_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2080_, 0, v_inst_2068_);
        leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
        v___x_2081_ = l_Lean_mkConst(v___x_2078_, v___x_2080_);
        v___x_2082_ = leanh::lean_apply_1(v_toExpr_2070_, v_val_2077_);
        v___x_2083_ = l_Lean_mkAppB(v___x_2081_, v_toTypeExpr_2069_, v___x_2082_);
        return v___x_2083_;
    }
}
pub unsafe fn l_Lean_instToExprOptionOfToLevel___redArg(
    mut v_inst_2086_: *mut leanh::LeanObject,
    mut v_inst_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toExpr_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2092_: u8 = 0;
    let mut v___f_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_2088_ = leanh::lean_ctor_get(v_inst_2087_, 0);
                v_toTypeExpr_2089_ = leanh::lean_ctor_get(v_inst_2087_, 1);
                v_isSharedCheck_2102_ = (!leanh::lean_is_exclusive(v_inst_2087_)) as u8;
                if v_isSharedCheck_2102_ == 0 {
                    v___x_2091_ = v_inst_2087_;
                    v_isShared_2092_ = v_isSharedCheck_2102_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toTypeExpr_2089_);
                    leanh::lean_inc(v_toExpr_2088_);
                    leanh::lean_dec(v_inst_2087_);
                    v___x_2091_ = leanh::lean_box(0);
                    v_isShared_2092_ = v_isSharedCheck_2102_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_toTypeExpr_2089_);
                leanh::lean_inc(v_inst_2086_);
                v___f_2093_ = leanh::lean_alloc_closure(
                    l_Lean_instToExprOptionOfToLevel___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2093_, 0, v_inst_2086_);
                leanh::lean_closure_set(v___f_2093_, 1, v_toTypeExpr_2089_);
                leanh::lean_closure_set(v___f_2093_, 2, v_toExpr_2088_);
                v___x_2094_ = l_Lean_instToExprOptionOfToLevel___redArg___closed__0;
                v___x_2095_ = leanh::lean_box(0);
                v___x_2096_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2096_, 0, v_inst_2086_);
                leanh::lean_ctor_set(v___x_2096_, 1, v___x_2095_);
                v___x_2097_ = l_Lean_mkConst(v___x_2094_, v___x_2096_);
                v___x_2098_ = l_Lean_Expr_app___override(v___x_2097_, v_toTypeExpr_2089_);
                if v_isShared_2092_ == 0 {
                    leanh::lean_ctor_set(v___x_2091_, 1, v___x_2098_);
                    leanh::lean_ctor_set(v___x_2091_, 0, v___f_2093_);
                    v___x_2100_ = v___x_2091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2101_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___f_2093_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___x_2098_);
                    v___x_2100_ = v_reuseFailAlloc_2101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToExprOptionOfToLevel(
    mut v_00_u03b1_2103_: *mut leanh::LeanObject,
    mut v_inst_2104_: *mut leanh::LeanObject,
    mut v_inst_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = l_Lean_instToExprOptionOfToLevel___redArg(v_inst_2104_, v_inst_2105_);
    return v___x_2106_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
    mut v_inst_2107_: *mut leanh::LeanObject,
    mut v_nilFn_2108_: *mut leanh::LeanObject,
    mut v_consFn_2109_: *mut leanh::LeanObject,
    mut v_x_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2110_) == 0 {
        leanh::lean_dec_ref(v_consFn_2109_);
        leanh::lean_dec_ref(v_inst_2107_);
        leanh::lean_inc_ref(v_nilFn_2108_);
        return v_nilFn_2108_;
    } else {
        let mut v_head_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toExpr_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_2111_ = leanh::lean_ctor_get(v_x_2110_, 0);
        leanh::lean_inc(v_head_2111_);
        v_tail_2112_ = leanh::lean_ctor_get(v_x_2110_, 1);
        leanh::lean_inc(v_tail_2112_);
        leanh::lean_dec_ref_known(v_x_2110_, 2);
        v_toExpr_2113_ = leanh::lean_ctor_get(v_inst_2107_, 0);
        leanh::lean_inc_ref(v_toExpr_2113_);
        v___x_2114_ = leanh::lean_apply_1(v_toExpr_2113_, v_head_2111_);
        leanh::lean_inc_ref(v_consFn_2109_);
        v___x_2115_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
            v_inst_2107_,
            v_nilFn_2108_,
            v_consFn_2109_,
            v_tail_2112_,
        );
        v___x_2116_ = l_Lean_mkAppB(v_consFn_2109_, v___x_2114_, v___x_2115_);
        return v___x_2116_;
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg___boxed(
    mut v_inst_2117_: *mut leanh::LeanObject,
    mut v_nilFn_2118_: *mut leanh::LeanObject,
    mut v_consFn_2119_: *mut leanh::LeanObject,
    mut v_x_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2121_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
        v_inst_2117_,
        v_nilFn_2118_,
        v_consFn_2119_,
        v_x_2120_,
    );
    leanh::lean_dec_ref(v_nilFn_2118_);
    return v_res_2121_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux(
    mut v_00_u03b1_2122_: *mut leanh::LeanObject,
    mut v_inst_2123_: *mut leanh::LeanObject,
    mut v_nilFn_2124_: *mut leanh::LeanObject,
    mut v_consFn_2125_: *mut leanh::LeanObject,
    mut v_x_2126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
        v_inst_2123_,
        v_nilFn_2124_,
        v_consFn_2125_,
        v_x_2126_,
    );
    return v___x_2127_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed(
    mut v_00_u03b1_2128_: *mut leanh::LeanObject,
    mut v_inst_2129_: *mut leanh::LeanObject,
    mut v_nilFn_2130_: *mut leanh::LeanObject,
    mut v_consFn_2131_: *mut leanh::LeanObject,
    mut v_x_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2133_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
        v_00_u03b1_2128_,
        v_inst_2129_,
        v_nilFn_2130_,
        v_consFn_2131_,
        v_x_2132_,
    );
    leanh::lean_dec_ref(v_nilFn_2130_);
    return v_res_2133_;
}
pub unsafe fn l_Lean_instToExprListOfToLevel___private__1___redArg(
    mut v_inst_2134_: *mut leanh::LeanObject,
    mut v_nil_2135_: *mut leanh::LeanObject,
    mut v_cons_2136_: *mut leanh::LeanObject,
    mut v_a_2137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2138_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
        v_inst_2134_,
        v_nil_2135_,
        v_cons_2136_,
        v_a_2137_,
    );
    return v___x_2138_;
}
pub unsafe fn l_Lean_instToExprListOfToLevel___private__1___redArg___boxed(
    mut v_inst_2139_: *mut leanh::LeanObject,
    mut v_nil_2140_: *mut leanh::LeanObject,
    mut v_cons_2141_: *mut leanh::LeanObject,
    mut v_a_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Lean_instToExprListOfToLevel___private__1___redArg(
        v_inst_2139_,
        v_nil_2140_,
        v_cons_2141_,
        v_a_2142_,
    );
    leanh::lean_dec_ref(v_nil_2140_);
    return v_res_2143_;
}
pub unsafe fn l_Lean_instToExprListOfToLevel___private__1(
    mut v_00_u03b1_2144_: *mut leanh::LeanObject,
    mut v_inst_2145_: *mut leanh::LeanObject,
    mut v_nil_2146_: *mut leanh::LeanObject,
    mut v_cons_2147_: *mut leanh::LeanObject,
    mut v_a_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2149_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
        v_inst_2145_,
        v_nil_2146_,
        v_cons_2147_,
        v_a_2148_,
    );
    return v___x_2149_;
}
pub unsafe fn l_Lean_instToExprListOfToLevel___private__1___boxed(
    mut v_00_u03b1_2150_: *mut leanh::LeanObject,
    mut v_inst_2151_: *mut leanh::LeanObject,
    mut v_nil_2152_: *mut leanh::LeanObject,
    mut v_cons_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l_Lean_instToExprListOfToLevel___private__1(
        v_00_u03b1_2150_,
        v_inst_2151_,
        v_nil_2152_,
        v_cons_2153_,
        v_a_2154_,
    );
    leanh::lean_dec_ref(v_nil_2152_);
    return v_res_2155_;
}
pub unsafe fn l_Lean_instToExprListOfToLevel___redArg(
    mut v_inst_2167_: *mut leanh::LeanObject,
    mut v_inst_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toTypeExpr_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toTypeExpr_2169_ = leanh::lean_ctor_get(v_inst_2168_, 1);
    leanh::lean_inc_ref_n(v_toTypeExpr_2169_, 3);
    v___x_2170_ = l_Lean_instToExprListOfToLevel___redArg___closed__2;
    v___x_2171_ = leanh::lean_box(0);
    v___x_2172_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2172_, 0, v_inst_2167_);
    leanh::lean_ctor_set(v___x_2172_, 1, v___x_2171_);
    leanh::lean_inc_ref_n(v___x_2172_, 2);
    v___x_2173_ = l_Lean_mkConst(v___x_2170_, v___x_2172_);
    v_nil_2174_ = l_Lean_Expr_app___override(v___x_2173_, v_toTypeExpr_2169_);
    v___x_2175_ = l_Lean_instToExprListOfToLevel___redArg___closed__4;
    v___x_2176_ = l_Lean_mkConst(v___x_2175_, v___x_2172_);
    v_cons_2177_ = l_Lean_Expr_app___override(v___x_2176_, v_toTypeExpr_2169_);
    v___x_2178_ = leanh::lean_alloc_closure(
        l_Lean_instToExprListOfToLevel___private__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_2178_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2178_, 1, v_inst_2168_);
    leanh::lean_closure_set(v___x_2178_, 2, v_nil_2174_);
    leanh::lean_closure_set(v___x_2178_, 3, v_cons_2177_);
    v___x_2179_ = l_Lean_instToExprListOfToLevel___redArg___closed__5;
    v___x_2180_ = l_Lean_mkConst(v___x_2179_, v___x_2172_);
    v___x_2181_ = l_Lean_Expr_app___override(v___x_2180_, v_toTypeExpr_2169_);
    v___x_2182_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2182_, 0, v___x_2178_);
    leanh::lean_ctor_set(v___x_2182_, 1, v___x_2181_);
    return v___x_2182_;
}
pub unsafe fn l_Lean_instToExprListOfToLevel(
    mut v_00_u03b1_2183_: *mut leanh::LeanObject,
    mut v_inst_2184_: *mut leanh::LeanObject,
    mut v_inst_2185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = l_Lean_instToExprListOfToLevel___redArg(v_inst_2184_, v_inst_2185_);
    return v___x_2186_;
}
pub unsafe fn l_Lean_instToExprArrayOfToLevel___redArg___lam__0(
    mut v_inst_2191_: *mut leanh::LeanObject,
    mut v_toTypeExpr_2192_: *mut leanh::LeanObject,
    mut v_inst_2193_: *mut leanh::LeanObject,
    mut v_as_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1;
    v___x_2196_ = leanh::lean_box(0);
    v___x_2197_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2197_, 0, v_inst_2191_);
    leanh::lean_ctor_set(v___x_2197_, 1, v___x_2196_);
    leanh::lean_inc_ref_n(v___x_2197_, 2);
    v___x_2198_ = l_Lean_mkConst(v___x_2195_, v___x_2197_);
    v___x_2199_ = l_Lean_instToExprListOfToLevel___redArg___closed__2;
    v___x_2200_ = l_Lean_mkConst(v___x_2199_, v___x_2197_);
    leanh::lean_inc_ref_n(v_toTypeExpr_2192_, 2);
    v_nil_2201_ = l_Lean_Expr_app___override(v___x_2200_, v_toTypeExpr_2192_);
    v___x_2202_ = l_Lean_instToExprListOfToLevel___redArg___closed__4;
    v___x_2203_ = l_Lean_mkConst(v___x_2202_, v___x_2197_);
    v_cons_2204_ = l_Lean_Expr_app___override(v___x_2203_, v_toTypeExpr_2192_);
    v___x_2205_ = lean_array_to_list(v_as_2194_);
    v___x_2206_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
        v_inst_2193_,
        v_nil_2201_,
        v_cons_2204_,
        v___x_2205_,
    );
    leanh::lean_dec_ref(v_nil_2201_);
    v___x_2207_ = l_Lean_mkAppB(v___x_2198_, v_toTypeExpr_2192_, v___x_2206_);
    return v___x_2207_;
}
pub unsafe fn l_Lean_instToExprArrayOfToLevel___redArg(
    mut v_inst_2211_: *mut leanh::LeanObject,
    mut v_inst_2212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toTypeExpr_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toTypeExpr_2213_ = leanh::lean_ctor_get(v_inst_2212_, 1);
    leanh::lean_inc_ref_n(v_toTypeExpr_2213_, 2);
    leanh::lean_inc(v_inst_2211_);
    v___f_2214_ = leanh::lean_alloc_closure(
        l_Lean_instToExprArrayOfToLevel___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2214_, 0, v_inst_2211_);
    leanh::lean_closure_set(v___f_2214_, 1, v_toTypeExpr_2213_);
    leanh::lean_closure_set(v___f_2214_, 2, v_inst_2212_);
    v___x_2215_ = l_Lean_instToExprArrayOfToLevel___redArg___closed__1;
    v___x_2216_ = leanh::lean_box(0);
    v___x_2217_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2217_, 0, v_inst_2211_);
    leanh::lean_ctor_set(v___x_2217_, 1, v___x_2216_);
    v___x_2218_ = l_Lean_mkConst(v___x_2215_, v___x_2217_);
    v___x_2219_ = l_Lean_Expr_app___override(v___x_2218_, v_toTypeExpr_2213_);
    v___x_2220_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2220_, 0, v___f_2214_);
    leanh::lean_ctor_set(v___x_2220_, 1, v___x_2219_);
    return v___x_2220_;
}
pub unsafe fn l_Lean_instToExprArrayOfToLevel(
    mut v_00_u03b1_2221_: *mut leanh::LeanObject,
    mut v_inst_2222_: *mut leanh::LeanObject,
    mut v_inst_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2224_ = l_Lean_instToExprArrayOfToLevel___redArg(v_inst_2222_, v_inst_2223_);
    return v___x_2224_;
}
pub unsafe fn l_Lean_instToExprProdOfToLevel___redArg___lam__0(
    mut v_inst_2229_: *mut leanh::LeanObject,
    mut v_inst_2230_: *mut leanh::LeanObject,
    mut v_toExpr_2231_: *mut leanh::LeanObject,
    mut v_toExpr_2232_: *mut leanh::LeanObject,
    mut v_toTypeExpr_2233_: *mut leanh::LeanObject,
    mut v_toTypeExpr_2234_: *mut leanh::LeanObject,
    mut v_x_2235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2236_ = leanh::lean_ctor_get(v_x_2235_, 0);
                v_snd_2237_ = leanh::lean_ctor_get(v_x_2235_, 1);
                v_isSharedCheck_2251_ = (!leanh::lean_is_exclusive(v_x_2235_)) as u8;
                if v_isSharedCheck_2251_ == 0 {
                    v___x_2239_ = v_x_2235_;
                    v_isShared_2240_ = v_isSharedCheck_2251_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2237_);
                    leanh::lean_inc(v_fst_2236_);
                    leanh::lean_dec(v_x_2235_);
                    v___x_2239_ = leanh::lean_box(0);
                    v_isShared_2240_ = v_isSharedCheck_2251_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2241_ = l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1;
                v___x_2242_ = leanh::lean_box(0);
                if v_isShared_2240_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2239_, 1);
                    leanh::lean_ctor_set(v___x_2239_, 1, v___x_2242_);
                    leanh::lean_ctor_set(v___x_2239_, 0, v_inst_2229_);
                    v___x_2244_ = v___x_2239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_inst_2229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 1, v___x_2242_);
                    v___x_2244_ = v_reuseFailAlloc_2250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2245_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2245_, 0, v_inst_2230_);
                leanh::lean_ctor_set(v___x_2245_, 1, v___x_2244_);
                v___x_2246_ = l_Lean_mkConst(v___x_2241_, v___x_2245_);
                v___x_2247_ = leanh::lean_apply_1(v_toExpr_2231_, v_fst_2236_);
                v___x_2248_ = leanh::lean_apply_1(v_toExpr_2232_, v_snd_2237_);
                v___x_2249_ = l_Lean_mkApp4(
                    v___x_2246_,
                    v_toTypeExpr_2233_,
                    v_toTypeExpr_2234_,
                    v___x_2247_,
                    v___x_2248_,
                );
                return v___x_2249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToExprProdOfToLevel___redArg(
    mut v_inst_2254_: *mut leanh::LeanObject,
    mut v_inst_2255_: *mut leanh::LeanObject,
    mut v_inst_2256_: *mut leanh::LeanObject,
    mut v_inst_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toExpr_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v_toExpr_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTypeExpr_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___f_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toExpr_2258_ = leanh::lean_ctor_get(v_inst_2256_, 0);
                v_toTypeExpr_2259_ = leanh::lean_ctor_get(v_inst_2256_, 1);
                v_isSharedCheck_2281_ = (!leanh::lean_is_exclusive(v_inst_2256_)) as u8;
                if v_isSharedCheck_2281_ == 0 {
                    v___x_2261_ = v_inst_2256_;
                    v_isShared_2262_ = v_isSharedCheck_2281_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toTypeExpr_2259_);
                    leanh::lean_inc(v_toExpr_2258_);
                    leanh::lean_dec(v_inst_2256_);
                    v___x_2261_ = leanh::lean_box(0);
                    v_isShared_2262_ = v_isSharedCheck_2281_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toExpr_2263_ = leanh::lean_ctor_get(v_inst_2257_, 0);
                v_toTypeExpr_2264_ = leanh::lean_ctor_get(v_inst_2257_, 1);
                v_isSharedCheck_2280_ = (!leanh::lean_is_exclusive(v_inst_2257_)) as u8;
                if v_isSharedCheck_2280_ == 0 {
                    v___x_2266_ = v_inst_2257_;
                    v_isShared_2267_ = v_isSharedCheck_2280_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toTypeExpr_2264_);
                    leanh::lean_inc(v_toExpr_2263_);
                    leanh::lean_dec(v_inst_2257_);
                    v___x_2266_ = leanh::lean_box(0);
                    v_isShared_2267_ = v_isSharedCheck_2280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_toTypeExpr_2264_);
                leanh::lean_inc_ref(v_toTypeExpr_2259_);
                leanh::lean_inc(v_inst_2254_);
                leanh::lean_inc(v_inst_2255_);
                v___f_2268_ = leanh::lean_alloc_closure(
                    l_Lean_instToExprProdOfToLevel___redArg___lam__0 as *mut core::ffi::c_void,
                    7,
                    6,
                );
                leanh::lean_closure_set(v___f_2268_, 0, v_inst_2255_);
                leanh::lean_closure_set(v___f_2268_, 1, v_inst_2254_);
                leanh::lean_closure_set(v___f_2268_, 2, v_toExpr_2258_);
                leanh::lean_closure_set(v___f_2268_, 3, v_toExpr_2263_);
                leanh::lean_closure_set(v___f_2268_, 4, v_toTypeExpr_2259_);
                leanh::lean_closure_set(v___f_2268_, 5, v_toTypeExpr_2264_);
                v___x_2269_ = l_Lean_instToExprProdOfToLevel___redArg___closed__0;
                v___x_2270_ = leanh::lean_box(0);
                if v_isShared_2262_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2261_, 1);
                    leanh::lean_ctor_set(v___x_2261_, 1, v___x_2270_);
                    leanh::lean_ctor_set(v___x_2261_, 0, v_inst_2255_);
                    v___x_2272_ = v___x_2261_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2279_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_inst_2255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___x_2270_);
                    v___x_2272_ = v_reuseFailAlloc_2279_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2273_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2273_, 0, v_inst_2254_);
                leanh::lean_ctor_set(v___x_2273_, 1, v___x_2272_);
                v___x_2274_ = l_Lean_mkConst(v___x_2269_, v___x_2273_);
                v___x_2275_ = l_Lean_mkAppB(v___x_2274_, v_toTypeExpr_2259_, v_toTypeExpr_2264_);
                if v_isShared_2267_ == 0 {
                    leanh::lean_ctor_set(v___x_2266_, 1, v___x_2275_);
                    leanh::lean_ctor_set(v___x_2266_, 0, v___f_2268_);
                    v___x_2277_ = v___x_2266_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___f_2268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2275_);
                    v___x_2277_ = v_reuseFailAlloc_2278_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToExprProdOfToLevel(
    mut v_00_u03b1_2282_: *mut leanh::LeanObject,
    mut v_00_u03b2_2283_: *mut leanh::LeanObject,
    mut v_inst_2284_: *mut leanh::LeanObject,
    mut v_inst_2285_: *mut leanh::LeanObject,
    mut v_inst_2286_: *mut leanh::LeanObject,
    mut v_inst_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2288_ = l_Lean_instToExprProdOfToLevel___redArg(
        v_inst_2284_,
        v_inst_2285_,
        v_inst_2286_,
        v_inst_2287_,
    );
    return v___x_2288_;
}
pub unsafe fn _init_l_Lean_instToExprLiteral___lam__0___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ = leanh::lean_box(0);
    v___x_2296_ = l_Lean_instToExprLiteral___lam__0___closed__2;
    v___x_2297_ = l_Lean_mkConst(v___x_2296_, v___x_2295_);
    return v___x_2297_;
}
pub unsafe fn _init_l_Lean_instToExprLiteral___lam__0___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = leanh::lean_box(0);
    v___x_2304_ = l_Lean_instToExprLiteral___lam__0___closed__5;
    v___x_2305_ = l_Lean_mkConst(v___x_2304_, v___x_2303_);
    return v___x_2305_;
}
pub unsafe fn l_Lean_instToExprLiteral___lam__0(
    mut v_l_2306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_l_2306_) == 0 {
        let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2307_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___lam__0___closed__3_once),
            _init_l_Lean_instToExprLiteral___lam__0___closed__3,
        );
        v___x_2308_ = l_Lean_Expr_lit___override(v_l_2306_);
        v___x_2309_ = l_Lean_Expr_app___override(v___x_2307_, v___x_2308_);
        return v___x_2309_;
    } else {
        let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2310_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___lam__0___closed__6),
            core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___lam__0___closed__6_once),
            _init_l_Lean_instToExprLiteral___lam__0___closed__6,
        );
        v___x_2311_ = l_Lean_Expr_lit___override(v_l_2306_);
        v___x_2312_ = l_Lean_Expr_app___override(v___x_2310_, v___x_2311_);
        return v___x_2312_;
    }
}
pub unsafe fn _init_l_Lean_instToExprLiteral___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2317_ = leanh::lean_box(0);
    v___x_2318_ = l_Lean_instToExprLiteral___closed__1;
    v___x_2319_ = l_Lean_mkConst(v___x_2318_, v___x_2317_);
    return v___x_2319_;
}
pub unsafe fn _init_l_Lean_instToExprLiteral___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2320_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___closed__2_once),
        _init_l_Lean_instToExprLiteral___closed__2,
    );
    v___f_2321_ = l_Lean_instToExprLiteral___closed__0;
    v___x_2322_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2322_, 0, v___f_2321_);
    leanh::lean_ctor_set(v___x_2322_, 1, v___x_2320_);
    return v___x_2322_;
}
pub unsafe fn _init_l_Lean_instToExprLiteral() -> *mut leanh::LeanObject {
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2323_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprLiteral___closed__3_once),
        _init_l_Lean_instToExprLiteral___closed__3,
    );
    return v___x_2323_;
}
pub unsafe fn _init_l_Lean_instToExprFVarId___lam__0___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = leanh::lean_box(0);
    v___x_2330_ = l_Lean_instToExprFVarId___lam__0___closed__1;
    v___x_2331_ = l_Lean_mkConst(v___x_2330_, v___x_2329_);
    return v___x_2331_;
}
pub unsafe fn l_Lean_instToExprFVarId___lam__0(
    mut v_fvarId_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFVarId___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprFVarId___lam__0___closed__2_once),
        _init_l_Lean_instToExprFVarId___lam__0___closed__2,
    );
    v___x_2334_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_fvarId_2332_);
    v___x_2335_ = l_Lean_Expr_app___override(v___x_2333_, v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn _init_l_Lean_instToExprFVarId___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2340_ = leanh::lean_box(0);
    v___x_2341_ = l_Lean_instToExprFVarId___closed__1;
    v___x_2342_ = l_Lean_mkConst(v___x_2341_, v___x_2340_);
    return v___x_2342_;
}
pub unsafe fn _init_l_Lean_instToExprFVarId___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFVarId___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprFVarId___closed__2_once),
        _init_l_Lean_instToExprFVarId___closed__2,
    );
    v___f_2344_ = l_Lean_instToExprFVarId___closed__0;
    v___x_2345_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2345_, 0, v___f_2344_);
    leanh::lean_ctor_set(v___x_2345_, 1, v___x_2343_);
    return v___x_2345_;
}
pub unsafe fn _init_l_Lean_instToExprFVarId() -> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprFVarId___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprFVarId___closed__3_once),
        _init_l_Lean_instToExprFVarId___closed__3,
    );
    return v___x_2346_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = leanh::lean_box(0);
    v___x_2356_ = l_Lean_instToExprPreresolved___lam__0___closed__3;
    v___x_2357_ = l_Lean_Expr_const___override(v___x_2356_, v___x_2355_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = leanh::lean_box(0);
    v___x_2365_ = l_Lean_instToExprPreresolved___lam__0___closed__6;
    v___x_2366_ = l_Lean_Expr_const___override(v___x_2365_, v___x_2364_);
    return v___x_2366_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___lam__0___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ = l_Lean_instToExprPreresolved___lam__0___closed__8;
    v___x_2371_ = l_Lean_instToExprListOfToLevel___redArg___closed__2;
    v___x_2372_ = l_Lean_mkConst(v___x_2371_, v___x_2370_);
    return v___x_2372_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___lam__0___closed__10()
-> *mut leanh::LeanObject {
    let mut v_type_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_2373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__3_once),
        _init_l_Lean_instToExprString___closed__3,
    );
    v___x_2374_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__9_once),
        _init_l_Lean_instToExprPreresolved___lam__0___closed__9,
    );
    v_nil_2375_ = l_Lean_Expr_app___override(v___x_2374_, v_type_2373_);
    return v_nil_2375_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = l_Lean_instToExprPreresolved___lam__0___closed__8;
    v___x_2377_ = l_Lean_instToExprListOfToLevel___redArg___closed__4;
    v___x_2378_ = l_Lean_mkConst(v___x_2377_, v___x_2376_);
    return v___x_2378_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___lam__0___closed__12()
-> *mut leanh::LeanObject {
    let mut v_type_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_2379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprString___closed__3_once),
        _init_l_Lean_instToExprString___closed__3,
    );
    v___x_2380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__11),
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__11_once),
        _init_l_Lean_instToExprPreresolved___lam__0___closed__11,
    );
    v_cons_2381_ = l_Lean_Expr_app___override(v___x_2380_, v_type_2379_);
    return v_cons_2381_;
}
pub unsafe fn l_Lean_instToExprPreresolved___lam__0(
    mut v___x_2382_: *mut leanh::LeanObject,
    mut v_x_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2383_) == 0 {
        let mut v_ns_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2382_);
        v_ns_2384_ = leanh::lean_ctor_get(v_x_2383_, 0);
        leanh::lean_inc(v_ns_2384_);
        leanh::lean_dec_ref_known(v_x_2383_, 1);
        v___x_2385_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__4_once),
            _init_l_Lean_instToExprPreresolved___lam__0___closed__4,
        );
        v___x_2386_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_ns_2384_);
        v___x_2387_ = l_Lean_Expr_app___override(v___x_2385_, v___x_2386_);
        return v___x_2387_;
    } else {
        let mut v_n_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fields_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_nil_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_cons_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_n_2388_ = leanh::lean_ctor_get(v_x_2383_, 0);
        leanh::lean_inc(v_n_2388_);
        v_fields_2389_ = leanh::lean_ctor_get(v_x_2383_, 1);
        leanh::lean_inc(v_fields_2389_);
        leanh::lean_dec_ref_known(v_x_2383_, 2);
        v___x_2390_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__7),
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__7_once),
            _init_l_Lean_instToExprPreresolved___lam__0___closed__7,
        );
        v___x_2391_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_n_2388_);
        v_nil_2392_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__10),
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__10_once),
            _init_l_Lean_instToExprPreresolved___lam__0___closed__10,
        );
        v_cons_2393_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__12),
            core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___lam__0___closed__12_once),
            _init_l_Lean_instToExprPreresolved___lam__0___closed__12,
        );
        v___x_2394_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(
            v___x_2382_,
            v_nil_2392_,
            v_cons_2393_,
            v_fields_2389_,
        );
        v___x_2395_ = l_Lean_mkAppB(v___x_2390_, v___x_2391_, v___x_2394_);
        return v___x_2395_;
    }
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2396_ = l_Lean_instToExprString;
    v___f_2397_ = leanh::lean_alloc_closure(
        l_Lean_instToExprPreresolved___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2397_, 0, v___x_2396_);
    return v___f_2397_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = leanh::lean_box(0);
    v___x_2403_ = l_Lean_instToExprPreresolved___closed__1;
    v___x_2404_ = l_Lean_Expr_const___override(v___x_2403_, v___x_2402_);
    return v___x_2404_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___closed__2_once),
        _init_l_Lean_instToExprPreresolved___closed__2,
    );
    v___f_2406_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___closed__0_once),
        _init_l_Lean_instToExprPreresolved___closed__0,
    );
    v___x_2407_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2407_, 0, v___f_2406_);
    leanh::lean_ctor_set(v___x_2407_, 1, v___x_2405_);
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_instToExprPreresolved() -> *mut leanh::LeanObject {
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2408_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instToExprPreresolved___closed__3_once),
        _init_l_Lean_instToExprPreresolved___closed__3,
    );
    return v___x_2408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ToExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ToLevel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instToExprNat = _init_l_Lean_instToExprNat();
    leanh::lean_mark_persistent(l_Lean_instToExprNat);
    l_Lean_instToExprInt = _init_l_Lean_instToExprInt();
    leanh::lean_mark_persistent(l_Lean_instToExprInt);
    l_Lean_instToExprRat = _init_l_Lean_instToExprRat();
    leanh::lean_mark_persistent(l_Lean_instToExprRat);
    l_Lean_instToExprUInt8 = _init_l_Lean_instToExprUInt8();
    leanh::lean_mark_persistent(l_Lean_instToExprUInt8);
    l_Lean_instToExprUInt16 = _init_l_Lean_instToExprUInt16();
    leanh::lean_mark_persistent(l_Lean_instToExprUInt16);
    l_Lean_instToExprUInt32 = _init_l_Lean_instToExprUInt32();
    leanh::lean_mark_persistent(l_Lean_instToExprUInt32);
    l_Lean_instToExprUInt64 = _init_l_Lean_instToExprUInt64();
    leanh::lean_mark_persistent(l_Lean_instToExprUInt64);
    l_Lean_instToExprUSize = _init_l_Lean_instToExprUSize();
    leanh::lean_mark_persistent(l_Lean_instToExprUSize);
    l_Lean_instToExprInt8 = _init_l_Lean_instToExprInt8();
    leanh::lean_mark_persistent(l_Lean_instToExprInt8);
    l_Lean_instToExprInt16 = _init_l_Lean_instToExprInt16();
    leanh::lean_mark_persistent(l_Lean_instToExprInt16);
    l_Lean_instToExprInt32 = _init_l_Lean_instToExprInt32();
    leanh::lean_mark_persistent(l_Lean_instToExprInt32);
    l_Lean_instToExprInt64 = _init_l_Lean_instToExprInt64();
    leanh::lean_mark_persistent(l_Lean_instToExprInt64);
    l_Lean_instToExprISize = _init_l_Lean_instToExprISize();
    leanh::lean_mark_persistent(l_Lean_instToExprISize);
    l_Lean_instToExprBool = _init_l_Lean_instToExprBool();
    leanh::lean_mark_persistent(l_Lean_instToExprBool);
    l_Lean_instToExprChar = _init_l_Lean_instToExprChar();
    leanh::lean_mark_persistent(l_Lean_instToExprChar);
    l_Lean_instToExprString = _init_l_Lean_instToExprString();
    leanh::lean_mark_persistent(l_Lean_instToExprString);
    l_Lean_instToExprUnit = _init_l_Lean_instToExprUnit();
    leanh::lean_mark_persistent(l_Lean_instToExprUnit);
    l_Lean_instToExprFilePath = _init_l_Lean_instToExprFilePath();
    leanh::lean_mark_persistent(l_Lean_instToExprFilePath);
    l_Lean_instToExprName = _init_l_Lean_instToExprName();
    leanh::lean_mark_persistent(l_Lean_instToExprName);
    l_Lean_instToExprLiteral = _init_l_Lean_instToExprLiteral();
    leanh::lean_mark_persistent(l_Lean_instToExprLiteral);
    l_Lean_instToExprFVarId = _init_l_Lean_instToExprFVarId();
    leanh::lean_mark_persistent(l_Lean_instToExprFVarId);
    l_Lean_instToExprPreresolved = _init_l_Lean_instToExprPreresolved();
    leanh::lean_mark_persistent(l_Lean_instToExprPreresolved);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ToExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ToExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ToLevel(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_ToExpr(builtin);
}