// Lean compiler output
// Module: Init.Data.FloatArray.Basic
// Imports: Init.Data.Float Init.Ext Init.GetElem Init.Data.ToString.Extra
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_float_array_data,
    lean_float_array_fget, lean_float_array_fset, lean_float_array_get, lean_float_array_mk,
    lean_float_array_push, lean_float_array_set, lean_float_array_size, lean_float_array_uget,
    lean_float_array_uset, lean_float_beq, lean_mk_empty_float_array, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_sarray_size,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Float::{
    initialize_Init_Data_Float, l_Float_toString___boxed, runtime_initialize_Init_Data_Float,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, l_List_toString___redArg,
    runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::GetElem::{initialize_Init_GetElem, runtime_initialize_Init_GetElem};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
pub static l_FloatArray_instBEq___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_FloatArray_instBEq_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_instBEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_FloatArray_instBEq: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_instBEq___closed__0_value) as *mut leanh::LeanObject;
static mut l_FloatArray_empty___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_empty___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_FloatArray_empty: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_FloatArray_instInhabited: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_FloatArray_instEmptyCollection: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_FloatArray_get___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_FloatArray_get___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_FloatArray_get___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_FloatArray_get___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_FloatArray_get___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_FloatArray_get___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_FloatArray_get___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_FloatArray_get___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_FloatArray_get___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_FloatArray_get___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_FloatArray_get___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__6_value: leanh::LeanStringObject<19> =
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_FloatArray_get___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_FloatArray_get___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_FloatArray_get___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_FloatArray_get___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_FloatArray_get___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_FloatArray_get___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_FloatArray_get___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_FloatArray_get___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__10_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116,
            105, 99, 0,
        ],
    };
static mut l_FloatArray_get___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            3731765604234633101 as *mut leanh::LeanObject,
        ],
    };
static mut l_FloatArray_get___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_get___auto__1___closed__12_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_FloatArray_get___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_get___auto__1___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_FloatArray_get___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_FloatArray_get___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_FloatArray_get___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_FloatArray_get___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_FloatArray_instGetElemNatFloatLtSize___closed__0_value:
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
    m_fun: l_FloatArray_instGetElemNatFloatLtSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_FloatArray_instGetElemNatFloatLtSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_instGetElemNatFloatLtSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_FloatArray_instGetElemNatFloatLtSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_instGetElemNatFloatLtSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0_value:
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
    m_fun: l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_FloatArray_instGetElemUSizeFloatLtNatToNatSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_FloatArray_uset___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_FloatArray_set___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_FloatArray_foldl___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_foldl___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_foldl___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_foldl___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_foldl___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_foldl___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_foldl___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_FloatArray_foldl___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_FloatArray_foldl___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_FloatArray_foldl___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_FloatArray_foldl___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_FloatArray_foldl___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_FloatArray_foldl___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_instToStringFloatArray___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Float_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instToStringFloatArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFloatArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instToStringFloatArray___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringFloatArray___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_instToStringFloatArray___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instToStringFloatArray___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFloatArray___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_instToStringFloatArray: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instToStringFloatArray___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_FloatArray_mk___boxed(
    mut v_data_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = lean_float_array_mk(v_data_711_);
    return v_res_712_;
}
pub unsafe fn l_FloatArray_data___boxed(
    mut v_self_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ = lean_float_array_data(v_self_714_);
    return v_res_715_;
}
pub unsafe fn l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(
    mut v_xs_716_: *mut leanh::LeanObject,
    mut v_ys_717_: *mut leanh::LeanObject,
    mut v_x_718_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_720_: u8 = 0;
    let mut v_one_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: f64 = 0.0;
    let mut v___x_726_: f64 = 0.0;
    let mut v___x_727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_719_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_720_ = lean_nat_dec_eq(v_x_718_, v_zero_719_);
                if v_isZero_720_ == 1 {
                    leanh::lean_dec(v_x_718_);
                    return v_isZero_720_;
                } else {
                    v_one_721_ = leanh::lean_unsigned_to_nat(1);
                    v_n_722_ = lean_nat_sub(v_x_718_, v_one_721_);
                    leanh::lean_dec(v_x_718_);
                    v___x_723_ = lean_array_fget_borrowed(v_xs_716_, v_n_722_);
                    v___x_724_ = lean_array_fget_borrowed(v_ys_717_, v_n_722_);
                    v___x_725_ = leanh::lean_unbox_float(v___x_723_);
                    v___x_726_ = leanh::lean_unbox_float(v___x_724_);
                    v___x_727_ = lean_float_beq(v___x_725_, v___x_726_);
                    if v___x_727_ == 0 {
                        leanh::lean_dec(v_n_722_);
                        return v___x_727_;
                    } else {
                        v_x_718_ = v_n_722_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg___boxed(
    mut v_xs_729_: *mut leanh::LeanObject,
    mut v_ys_730_: *mut leanh::LeanObject,
    mut v_x_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_732_: u8 = 0;
    let mut v_r_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_732_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(
        v_xs_729_, v_ys_730_, v_x_731_,
    );
    leanh::lean_dec_ref(v_ys_730_);
    leanh::lean_dec_ref(v_xs_729_);
    v_r_733_ = leanh::lean_box((v_res_732_) as usize);
    return v_r_733_;
}
pub unsafe fn l_FloatArray_instBEq_beq(
    mut v_x_734_: *mut leanh::LeanObject,
    mut v_x_735_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_data_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    v_data_736_ = lean_float_array_data(v_x_734_);
    v_data_737_ = lean_float_array_data(v_x_735_);
    v___x_738_ = lean_array_get_size(v_data_736_);
    v___x_739_ = lean_array_get_size(v_data_737_);
    v___x_740_ = lean_nat_dec_eq(v___x_738_, v___x_739_);
    if v___x_740_ == 0 {
        leanh::lean_dec_ref(v_data_737_);
        leanh::lean_dec_ref(v_data_736_);
        return v___x_740_;
    } else {
        let mut v___x_741_: u8 = 0;
        v___x_741_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(
            v_data_736_,
            v_data_737_,
            v___x_738_,
        );
        leanh::lean_dec_ref(v_data_737_);
        leanh::lean_dec_ref(v_data_736_);
        return v___x_741_;
    }
}
pub unsafe fn l_FloatArray_instBEq_beq___boxed(
    mut v_x_742_: *mut leanh::LeanObject,
    mut v_x_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_744_: u8 = 0;
    let mut v_r_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ = l_FloatArray_instBEq_beq(v_x_742_, v_x_743_);
    v_r_745_ = leanh::lean_box((v_res_744_) as usize);
    return v_r_745_;
}
pub unsafe fn l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(
    mut v_xs_746_: *mut leanh::LeanObject,
    mut v_ys_747_: *mut leanh::LeanObject,
    mut v_hsz_748_: *mut leanh::LeanObject,
    mut v_x_749_: *mut leanh::LeanObject,
    mut v_x_750_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_751_: u8 = 0;
    v___x_751_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___redArg(
        v_xs_746_, v_ys_747_, v_x_749_,
    );
    return v___x_751_;
}
pub unsafe fn l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0___boxed(
    mut v_xs_752_: *mut leanh::LeanObject,
    mut v_ys_753_: *mut leanh::LeanObject,
    mut v_hsz_754_: *mut leanh::LeanObject,
    mut v_x_755_: *mut leanh::LeanObject,
    mut v_x_756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_757_: u8 = 0;
    let mut v_r_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Array_isEqvAux___at___00FloatArray_instBEq_beq_spec__0(
        v_xs_752_, v_ys_753_, v_hsz_754_, v_x_755_, v_x_756_,
    );
    leanh::lean_dec_ref(v_ys_753_);
    leanh::lean_dec_ref(v_xs_752_);
    v_r_758_ = leanh::lean_box((v_res_757_) as usize);
    return v_r_758_;
}
pub unsafe fn l_FloatArray_emptyWithCapacity___boxed(
    mut v_c_762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_763_ = lean_mk_empty_float_array(v_c_762_);
    leanh::lean_dec(v_c_762_);
    return v_res_763_;
}
pub unsafe fn _init_l_FloatArray_empty___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = leanh::lean_unsigned_to_nat(0);
    v___x_765_ = lean_mk_empty_float_array(v___x_764_);
    return v___x_765_;
}
pub unsafe fn _init_l_FloatArray_empty() -> *mut leanh::LeanObject {
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_empty___closed__0),
        core::ptr::addr_of_mut!(l_FloatArray_empty___closed__0_once),
        _init_l_FloatArray_empty___closed__0,
    );
    return v___x_766_;
}
pub unsafe fn _init_l_FloatArray_instInhabited() -> *mut leanh::LeanObject {
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_767_ = l_FloatArray_empty;
    return v___x_767_;
}
pub unsafe fn _init_l_FloatArray_instEmptyCollection() -> *mut leanh::LeanObject {
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = l_FloatArray_empty;
    return v___x_768_;
}
pub unsafe fn l_FloatArray_push___boxed(
    mut v_a_00___x40___internal___hyg_771_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_2__boxed_773_: f64 = 0.0;
    let mut v_res_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_2__boxed_773_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_772_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_772_);
    v_res_774_ = lean_float_array_push(
        v_a_00___x40___internal___hyg_771_,
        v_a_00___x40___internal___hyg_2__boxed_773_,
    );
    return v_res_774_;
}
pub unsafe fn l_FloatArray_size___boxed(
    mut v_a_00___x40___internal___hyg_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = lean_float_array_size(v_a_00___x40___internal___hyg_776_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_776_);
    return v_res_777_;
}
pub unsafe fn l_FloatArray_usize___boxed(
    mut v_a_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_780_: usize = 0;
    let mut v_r_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = lean_sarray_size(v_a_779_);
    leanh::lean_dec_ref(v_a_779_);
    v_r_781_ = leanh::lean_box_usize(v_res_780_);
    return v_r_781_;
}
pub unsafe fn l_FloatArray_uget___boxed(
    mut v_a_785_: *mut leanh::LeanObject,
    mut v_i_786_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_788_: usize = 0;
    let mut v_res_789_: f64 = 0.0;
    let mut v_r_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_788_ = leanh::lean_unbox_usize(v_i_786_);
    leanh::lean_dec(v_i_786_);
    v_res_789_ = lean_float_array_uget(v_a_785_, v_i_boxed_788_);
    leanh::lean_dec_ref(v_a_785_);
    v_r_790_ = leanh::lean_box_float(v_res_789_);
    return v_r_790_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_FloatArray_get___auto__1___closed__12;
    v___x_816_ = l_Lean_mkAtom(v___x_815_);
    return v___x_816_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__14() -> *mut leanh::LeanObject {
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__13_once),
        _init_l_FloatArray_get___auto__1___closed__13,
    );
    v___x_818_ = l_FloatArray_get___auto__1___closed__5;
    v___x_819_ = lean_array_push(v___x_818_, v___x_817_);
    return v___x_819_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__14_once),
        _init_l_FloatArray_get___auto__1___closed__14,
    );
    v___x_821_ = l_FloatArray_get___auto__1___closed__11;
    v___x_822_ = leanh::lean_box(2);
    v___x_823_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_823_, 0, v___x_822_);
    leanh::lean_ctor_set(v___x_823_, 1, v___x_821_);
    leanh::lean_ctor_set(v___x_823_, 2, v___x_820_);
    return v___x_823_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__15_once),
        _init_l_FloatArray_get___auto__1___closed__15,
    );
    v___x_825_ = l_FloatArray_get___auto__1___closed__5;
    v___x_826_ = lean_array_push(v___x_825_, v___x_824_);
    return v___x_826_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__16_once),
        _init_l_FloatArray_get___auto__1___closed__16,
    );
    v___x_828_ = l_FloatArray_get___auto__1___closed__9;
    v___x_829_ = leanh::lean_box(2);
    v___x_830_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_830_, 0, v___x_829_);
    leanh::lean_ctor_set(v___x_830_, 1, v___x_828_);
    leanh::lean_ctor_set(v___x_830_, 2, v___x_827_);
    return v___x_830_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__17_once),
        _init_l_FloatArray_get___auto__1___closed__17,
    );
    v___x_832_ = l_FloatArray_get___auto__1___closed__5;
    v___x_833_ = lean_array_push(v___x_832_, v___x_831_);
    return v___x_833_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__18_once),
        _init_l_FloatArray_get___auto__1___closed__18,
    );
    v___x_835_ = l_FloatArray_get___auto__1___closed__7;
    v___x_836_ = leanh::lean_box(2);
    v___x_837_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_837_, 0, v___x_836_);
    leanh::lean_ctor_set(v___x_837_, 1, v___x_835_);
    leanh::lean_ctor_set(v___x_837_, 2, v___x_834_);
    return v___x_837_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__19_once),
        _init_l_FloatArray_get___auto__1___closed__19,
    );
    v___x_839_ = l_FloatArray_get___auto__1___closed__5;
    v___x_840_ = lean_array_push(v___x_839_, v___x_838_);
    return v___x_840_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__20_once),
        _init_l_FloatArray_get___auto__1___closed__20,
    );
    v___x_842_ = l_FloatArray_get___auto__1___closed__4;
    v___x_843_ = leanh::lean_box(2);
    v___x_844_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_844_, 0, v___x_843_);
    leanh::lean_ctor_set(v___x_844_, 1, v___x_842_);
    leanh::lean_ctor_set(v___x_844_, 2, v___x_841_);
    return v___x_844_;
}
pub unsafe fn _init_l_FloatArray_get___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_845_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__21_once),
        _init_l_FloatArray_get___auto__1___closed__21,
    );
    return v___x_845_;
}
pub unsafe fn l_FloatArray_get___boxed(
    mut v_ds_849_: *mut leanh::LeanObject,
    mut v_i_850_: *mut leanh::LeanObject,
    mut v_h_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_852_: f64 = 0.0;
    let mut v_r_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = lean_float_array_fget(v_ds_849_, v_i_850_);
    leanh::lean_dec(v_i_850_);
    leanh::lean_dec_ref(v_ds_849_);
    v_r_853_ = leanh::lean_box_float(v_res_852_);
    return v_r_853_;
}
pub unsafe fn l_FloatArray_get_x21___boxed(
    mut v_a_00___x40___internal___hyg_856_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_858_: f64 = 0.0;
    let mut v_r_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_858_ = lean_float_array_get(
        v_a_00___x40___internal___hyg_856_,
        v_a_00___x40___internal___hyg_857_,
    );
    leanh::lean_dec(v_a_00___x40___internal___hyg_857_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_856_);
    v_r_859_ = leanh::lean_box_float(v_res_858_);
    return v_r_859_;
}
pub unsafe fn l_FloatArray_get_x3f(
    mut v_ds_860_: *mut leanh::LeanObject,
    mut v_i_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: u8 = 0;
    v___x_862_ = lean_float_array_size(v_ds_860_);
    v___x_863_ = lean_nat_dec_lt(v_i_861_, v___x_862_);
    if v___x_863_ == 0 {
        let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_864_ = leanh::lean_box(0);
        return v___x_864_;
    } else {
        let mut v___x_865_: f64 = 0.0;
        let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_865_ = lean_float_array_fget(v_ds_860_, v_i_861_);
        v___x_866_ = leanh::lean_box_float(v___x_865_);
        v___x_867_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_867_, 0, v___x_866_);
        return v___x_867_;
    }
}
pub unsafe fn l_FloatArray_get_x3f___boxed(
    mut v_ds_868_: *mut leanh::LeanObject,
    mut v_i_869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_870_ = l_FloatArray_get_x3f(v_ds_868_, v_i_869_);
    leanh::lean_dec(v_i_869_);
    leanh::lean_dec_ref(v_ds_868_);
    return v_res_870_;
}
pub unsafe fn l_FloatArray_instGetElemNatFloatLtSize___lam__0(
    mut v_xs_871_: *mut leanh::LeanObject,
    mut v_i_872_: *mut leanh::LeanObject,
    mut v_h_873_: *mut leanh::LeanObject,
) -> f64 {
    let mut v___x_874_: f64 = 0.0;
    v___x_874_ = lean_float_array_fget(v_xs_871_, v_i_872_);
    return v___x_874_;
}
pub unsafe fn l_FloatArray_instGetElemNatFloatLtSize___lam__0___boxed(
    mut v_xs_875_: *mut leanh::LeanObject,
    mut v_i_876_: *mut leanh::LeanObject,
    mut v_h_877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_878_: f64 = 0.0;
    let mut v_r_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_FloatArray_instGetElemNatFloatLtSize___lam__0(v_xs_875_, v_i_876_, v_h_877_);
    leanh::lean_dec(v_i_876_);
    leanh::lean_dec_ref(v_xs_875_);
    v_r_879_ = leanh::lean_box_float(v_res_878_);
    return v_r_879_;
}
pub unsafe fn l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(
    mut v_xs_882_: *mut leanh::LeanObject,
    mut v_i_883_: usize,
    mut v_h_884_: *mut leanh::LeanObject,
) -> f64 {
    let mut v___x_885_: f64 = 0.0;
    v___x_885_ = lean_float_array_uget(v_xs_882_, v_i_883_);
    return v___x_885_;
}
pub unsafe fn l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0___boxed(
    mut v_xs_886_: *mut leanh::LeanObject,
    mut v_i_887_: *mut leanh::LeanObject,
    mut v_h_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_889_: usize = 0;
    let mut v_res_890_: f64 = 0.0;
    let mut v_r_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_889_ = leanh::lean_unbox_usize(v_i_887_);
    leanh::lean_dec(v_i_887_);
    v_res_890_ = l_FloatArray_instGetElemUSizeFloatLtNatToNatSize___lam__0(
        v_xs_886_,
        v_i_boxed_889_,
        v_h_888_,
    );
    leanh::lean_dec_ref(v_xs_886_);
    v_r_891_ = leanh::lean_box_float(v_res_890_);
    return v_r_891_;
}
pub unsafe fn _init_l_FloatArray_uset___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__21_once),
        _init_l_FloatArray_get___auto__1___closed__21,
    );
    return v___x_894_;
}
pub unsafe fn l_FloatArray_uset___boxed(
    mut v_a_899_: *mut leanh::LeanObject,
    mut v_i_900_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_901_: *mut leanh::LeanObject,
    mut v_h_902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_903_: usize = 0;
    let mut v_a_00___x40___internal___hyg_1__boxed_904_: f64 = 0.0;
    let mut v_res_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_903_ = leanh::lean_unbox_usize(v_i_900_);
    leanh::lean_dec(v_i_900_);
    v_a_00___x40___internal___hyg_1__boxed_904_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_901_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_901_);
    v_res_905_ = lean_float_array_uset(
        v_a_899_,
        v_i_boxed_903_,
        v_a_00___x40___internal___hyg_1__boxed_904_,
    );
    return v_res_905_;
}
pub unsafe fn _init_l_FloatArray_set___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_FloatArray_get___auto__1___closed__21_once),
        _init_l_FloatArray_get___auto__1___closed__21,
    );
    return v___x_906_;
}
pub unsafe fn l_FloatArray_set___boxed(
    mut v_ds_911_: *mut leanh::LeanObject,
    mut v_i_912_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_913_: *mut leanh::LeanObject,
    mut v_h_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_915_: f64 = 0.0;
    let mut v_res_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_915_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_913_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_913_);
    v_res_916_ = lean_float_array_fset(
        v_ds_911_,
        v_i_912_,
        v_a_00___x40___internal___hyg_1__boxed_915_,
    );
    leanh::lean_dec(v_i_912_);
    return v_res_916_;
}
pub unsafe fn l_FloatArray_set_x21___boxed(
    mut v_a_00___x40___internal___hyg_920_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_921_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_3__boxed_923_: f64 = 0.0;
    let mut v_res_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_3__boxed_923_ =
        leanh::lean_unbox_float(v_a_00___x40___internal___hyg_922_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_922_);
    v_res_924_ = lean_float_array_set(
        v_a_00___x40___internal___hyg_920_,
        v_a_00___x40___internal___hyg_921_,
        v_a_00___x40___internal___hyg_3__boxed_923_,
    );
    leanh::lean_dec(v_a_00___x40___internal___hyg_921_);
    return v_res_924_;
}
pub unsafe fn l_FloatArray_isEmpty(mut v_s_925_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: u8 = 0;
    v___x_926_ = lean_float_array_size(v_s_925_);
    v___x_927_ = leanh::lean_unsigned_to_nat(0);
    v___x_928_ = lean_nat_dec_eq(v___x_926_, v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_FloatArray_isEmpty___boxed(
    mut v_s_929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_930_: u8 = 0;
    let mut v_r_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_930_ = l_FloatArray_isEmpty(v_s_929_);
    leanh::lean_dec_ref(v_s_929_);
    v_r_931_ = leanh::lean_box((v_res_930_) as usize);
    return v_r_931_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(
    mut v_ds_932_: *mut leanh::LeanObject,
    mut v_i_933_: *mut leanh::LeanObject,
    mut v_r_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: f64 = 0.0;
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_935_ = lean_float_array_size(v_ds_932_);
                v___x_936_ = lean_nat_dec_lt(v_i_933_, v___x_935_);
                if v___x_936_ == 0 {
                    leanh::lean_dec(v_i_933_);
                    v___x_937_ = l_List_reverse___redArg(v_r_934_);
                    return v___x_937_;
                } else {
                    v___x_938_ = leanh::lean_unsigned_to_nat(1);
                    v___x_939_ = lean_nat_add(v_i_933_, v___x_938_);
                    v___x_940_ = lean_float_array_fget(v_ds_932_, v_i_933_);
                    leanh::lean_dec(v_i_933_);
                    v___x_941_ = leanh::lean_box_float(v___x_940_);
                    v___x_942_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_942_, 0, v___x_941_);
                    leanh::lean_ctor_set(v___x_942_, 1, v_r_934_);
                    v_i_933_ = v___x_939_;
                    v_r_934_ = v___x_942_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop___boxed(
    mut v_ds_944_: *mut leanh::LeanObject,
    mut v_i_945_: *mut leanh::LeanObject,
    mut v_r_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(
        v_ds_944_, v_i_945_, v_r_946_,
    );
    leanh::lean_dec_ref(v_ds_944_);
    return v_res_947_;
}
pub unsafe fn l_FloatArray_toList(
    mut v_ds_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = leanh::lean_unsigned_to_nat(0);
    v___x_950_ = leanh::lean_box(0);
    v___x_951_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_toList_loop(
        v_ds_948_, v___x_949_, v___x_950_,
    );
    return v___x_951_;
}
pub unsafe fn l_FloatArray_toList___boxed(
    mut v_ds_952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_953_ = l_FloatArray_toList(v_ds_952_);
    leanh::lean_dec_ref(v_ds_952_);
    return v_res_953_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed(
    mut v_toApplicative_954_: *mut leanh::LeanObject,
    mut v_i_955_: *mut leanh::LeanObject,
    mut v_inst_956_: *mut leanh::LeanObject,
    mut v_as_957_: *mut leanh::LeanObject,
    mut v_f_958_: *mut leanh::LeanObject,
    mut v_sz_959_: *mut leanh::LeanObject,
    mut v_____do__lift_960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_961_: usize = 0;
    let mut v_sz_boxed_962_: usize = 0;
    let mut v_res_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_961_ = leanh::lean_unbox_usize(v_i_955_);
    leanh::lean_dec(v_i_955_);
    v_sz_boxed_962_ = leanh::lean_unbox_usize(v_sz_959_);
    leanh::lean_dec(v_sz_959_);
    v_res_963_ =
        l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(
            v_toApplicative_954_,
            v_i_boxed_961_,
            v_inst_956_,
            v_as_957_,
            v_f_958_,
            v_sz_boxed_962_,
            v_____do__lift_960_,
        );
    return v_res_963_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(
    mut v_inst_964_: *mut leanh::LeanObject,
    mut v_as_965_: *mut leanh::LeanObject,
    mut v_f_966_: *mut leanh::LeanObject,
    mut v_sz_967_: usize,
    mut v_i_968_: usize,
    mut v_b_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_970_: u8 = 0;
    v___x_970_ = lean_usize_dec_lt(v_i_968_, v_sz_967_);
    if v___x_970_ == 0 {
        let mut v_toApplicative_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_966_);
        leanh::lean_dec_ref(v_as_965_);
        v_toApplicative_971_ = leanh::lean_ctor_get(v_inst_964_, 0);
        leanh::lean_inc_ref(v_toApplicative_971_);
        leanh::lean_dec_ref(v_inst_964_);
        v_toPure_972_ = leanh::lean_ctor_get(v_toApplicative_971_, 1);
        leanh::lean_inc(v_toPure_972_);
        leanh::lean_dec_ref(v_toApplicative_971_);
        v___x_973_ = leanh::lean_apply_2(v_toPure_972_, leanh::lean_box(0), v_b_969_);
        return v___x_973_;
    } else {
        let mut v_toApplicative_974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_978_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_979_: f64 = 0.0;
        let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_974_ = leanh::lean_ctor_get(v_inst_964_, 0);
        leanh::lean_inc_ref(v_toApplicative_974_);
        v_toBind_975_ = leanh::lean_ctor_get(v_inst_964_, 1);
        leanh::lean_inc(v_toBind_975_);
        v___x_976_ = leanh::lean_box_usize(v_i_968_);
        v___x_977_ = leanh::lean_box_usize(v_sz_967_);
        leanh::lean_inc(v_f_966_);
        leanh::lean_inc_ref(v_as_965_);
        v___f_978_ = leanh::lean_alloc_closure(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 6);
        leanh::lean_closure_set(v___f_978_, 0, v_toApplicative_974_);
        leanh::lean_closure_set(v___f_978_, 1, v___x_976_);
        leanh::lean_closure_set(v___f_978_, 2, v_inst_964_);
        leanh::lean_closure_set(v___f_978_, 3, v_as_965_);
        leanh::lean_closure_set(v___f_978_, 4, v_f_966_);
        leanh::lean_closure_set(v___f_978_, 5, v___x_977_);
        v_a_979_ = lean_float_array_uget(v_as_965_, v_i_968_);
        leanh::lean_dec_ref(v_as_965_);
        v___x_980_ = leanh::lean_box_float(v_a_979_);
        v___x_981_ = leanh::lean_apply_2(v_f_966_, v___x_980_, v_b_969_);
        v___x_982_ = leanh::lean_apply_4(
            v_toBind_975_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_981_,
            v___f_978_,
        );
        return v___x_982_;
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___lam__0(
    mut v_toApplicative_983_: *mut leanh::LeanObject,
    mut v_i_984_: usize,
    mut v_inst_985_: *mut leanh::LeanObject,
    mut v_as_986_: *mut leanh::LeanObject,
    mut v_f_987_: *mut leanh::LeanObject,
    mut v_sz_988_: usize,
    mut v_____do__lift_989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_989_) == 0 {
        let mut v_a_990_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_987_);
        leanh::lean_dec_ref(v_as_986_);
        leanh::lean_dec_ref(v_inst_985_);
        v_a_990_ = leanh::lean_ctor_get(v_____do__lift_989_, 0);
        leanh::lean_inc(v_a_990_);
        leanh::lean_dec_ref_known(v_____do__lift_989_, 1);
        v_toPure_991_ = leanh::lean_ctor_get(v_toApplicative_983_, 1);
        leanh::lean_inc(v_toPure_991_);
        leanh::lean_dec_ref(v_toApplicative_983_);
        v___x_992_ = leanh::lean_apply_2(v_toPure_991_, leanh::lean_box(0), v_a_990_);
        return v___x_992_;
    } else {
        let mut v_a_993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_994_: usize = 0;
        let mut v___x_995_: usize = 0;
        let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_983_);
        v_a_993_ = leanh::lean_ctor_get(v_____do__lift_989_, 0);
        leanh::lean_inc(v_a_993_);
        leanh::lean_dec_ref_known(v_____do__lift_989_, 1);
        v___x_994_ = 1usize;
        v___x_995_ = lean_usize_add(v_i_984_, v___x_994_);
        v___x_996_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(
            v_inst_985_,
            v_as_986_,
            v_f_987_,
            v_sz_988_,
            v___x_995_,
            v_a_993_,
        );
        return v___x_996_;
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg___boxed(
    mut v_inst_997_: *mut leanh::LeanObject,
    mut v_as_998_: *mut leanh::LeanObject,
    mut v_f_999_: *mut leanh::LeanObject,
    mut v_sz_1000_: *mut leanh::LeanObject,
    mut v_i_1001_: *mut leanh::LeanObject,
    mut v_b_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1003_: usize = 0;
    let mut v_i_boxed_1004_: usize = 0;
    let mut v_res_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1003_ = leanh::lean_unbox_usize(v_sz_1000_);
    leanh::lean_dec(v_sz_1000_);
    v_i_boxed_1004_ = leanh::lean_unbox_usize(v_i_1001_);
    leanh::lean_dec(v_i_1001_);
    v_res_1005_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(
        v_inst_997_,
        v_as_998_,
        v_f_999_,
        v_sz_boxed_1003_,
        v_i_boxed_1004_,
        v_b_1002_,
    );
    return v_res_1005_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(
    mut v_00_u03b2_1006_: *mut leanh::LeanObject,
    mut v_m_1007_: *mut leanh::LeanObject,
    mut v_inst_1008_: *mut leanh::LeanObject,
    mut v_as_1009_: *mut leanh::LeanObject,
    mut v_f_1010_: *mut leanh::LeanObject,
    mut v_sz_1011_: usize,
    mut v_i_1012_: usize,
    mut v_b_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(
        v_inst_1008_,
        v_as_1009_,
        v_f_1010_,
        v_sz_1011_,
        v_i_1012_,
        v_b_1013_,
    );
    return v___x_1014_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___boxed(
    mut v_00_u03b2_1015_: *mut leanh::LeanObject,
    mut v_m_1016_: *mut leanh::LeanObject,
    mut v_inst_1017_: *mut leanh::LeanObject,
    mut v_as_1018_: *mut leanh::LeanObject,
    mut v_f_1019_: *mut leanh::LeanObject,
    mut v_sz_1020_: *mut leanh::LeanObject,
    mut v_i_1021_: *mut leanh::LeanObject,
    mut v_b_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1023_: usize = 0;
    let mut v_i_boxed_1024_: usize = 0;
    let mut v_res_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1023_ = leanh::lean_unbox_usize(v_sz_1020_);
    leanh::lean_dec(v_sz_1020_);
    v_i_boxed_1024_ = leanh::lean_unbox_usize(v_i_1021_);
    leanh::lean_dec(v_i_1021_);
    v_res_1025_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop(
        v_00_u03b2_1015_,
        v_m_1016_,
        v_inst_1017_,
        v_as_1018_,
        v_f_1019_,
        v_sz_boxed_1023_,
        v_i_boxed_1024_,
        v_b_1022_,
    );
    return v_res_1025_;
}
pub unsafe fn l_FloatArray_forInUnsafe___redArg(
    mut v_inst_1026_: *mut leanh::LeanObject,
    mut v_as_1027_: *mut leanh::LeanObject,
    mut v_b_1028_: *mut leanh::LeanObject,
    mut v_f_1029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1030_: usize = 0;
    let mut v___x_1031_: usize = 0;
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1030_ = lean_sarray_size(v_as_1027_);
    v___x_1031_ = 0usize;
    v___x_1032_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(
        v_inst_1026_,
        v_as_1027_,
        v_f_1029_,
        v_sz_1030_,
        v___x_1031_,
        v_b_1028_,
    );
    return v___x_1032_;
}
pub unsafe fn l_FloatArray_forInUnsafe(
    mut v_00_u03b2_1033_: *mut leanh::LeanObject,
    mut v_m_1034_: *mut leanh::LeanObject,
    mut v_inst_1035_: *mut leanh::LeanObject,
    mut v_as_1036_: *mut leanh::LeanObject,
    mut v_b_1037_: *mut leanh::LeanObject,
    mut v_f_1038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1039_: usize = 0;
    let mut v___x_1040_: usize = 0;
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1039_ = lean_sarray_size(v_as_1036_);
    v___x_1040_ = 0usize;
    v___x_1041_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(
        v_inst_1035_,
        v_as_1036_,
        v_f_1038_,
        v_sz_1039_,
        v___x_1040_,
        v_b_1037_,
    );
    return v___x_1041_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed(
    mut v_toPure_1042_: *mut leanh::LeanObject,
    mut v_inst_1043_: *mut leanh::LeanObject,
    mut v_as_1044_: *mut leanh::LeanObject,
    mut v_f_1045_: *mut leanh::LeanObject,
    mut v_n_1046_: *mut leanh::LeanObject,
    mut v_____do__lift_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1048_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(
        v_toPure_1042_,
        v_inst_1043_,
        v_as_1044_,
        v_f_1045_,
        v_n_1046_,
        v_____do__lift_1047_,
    );
    leanh::lean_dec(v_n_1046_);
    return v_res_1048_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(
    mut v_inst_1049_: *mut leanh::LeanObject,
    mut v_as_1050_: *mut leanh::LeanObject,
    mut v_f_1051_: *mut leanh::LeanObject,
    mut v_i_1052_: *mut leanh::LeanObject,
    mut v_b_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1058_: u8 = 0;
    v_toApplicative_1054_ = leanh::lean_ctor_get(v_inst_1049_, 0);
    v_toBind_1055_ = leanh::lean_ctor_get(v_inst_1049_, 1);
    leanh::lean_inc(v_toBind_1055_);
    v_toPure_1056_ = leanh::lean_ctor_get(v_toApplicative_1054_, 1);
    leanh::lean_inc(v_toPure_1056_);
    v_zero_1057_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1058_ = lean_nat_dec_eq(v_i_1052_, v_zero_1057_);
    if v_isZero_1058_ == 1 {
        let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_1055_);
        leanh::lean_dec(v_f_1051_);
        leanh::lean_dec_ref(v_as_1050_);
        leanh::lean_dec_ref(v_inst_1049_);
        v___x_1059_ =
            leanh::lean_apply_2(v_toPure_1056_, leanh::lean_box(0), v_b_1053_);
        return v___x_1059_;
    } else {
        let mut v_one_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1066_: f64 = 0.0;
        let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_1060_ = leanh::lean_unsigned_to_nat(1);
        v_n_1061_ = lean_nat_sub(v_i_1052_, v_one_1060_);
        leanh::lean_inc(v_n_1061_);
        leanh::lean_inc(v_f_1051_);
        leanh::lean_inc_ref(v_as_1050_);
        v___f_1062_ = leanh::lean_alloc_closure(l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_1062_, 0, v_toPure_1056_);
        leanh::lean_closure_set(v___f_1062_, 1, v_inst_1049_);
        leanh::lean_closure_set(v___f_1062_, 2, v_as_1050_);
        leanh::lean_closure_set(v___f_1062_, 3, v_f_1051_);
        leanh::lean_closure_set(v___f_1062_, 4, v_n_1061_);
        v___x_1063_ = lean_float_array_size(v_as_1050_);
        v___x_1064_ = lean_nat_sub(v___x_1063_, v_one_1060_);
        v___x_1065_ = lean_nat_sub(v___x_1064_, v_n_1061_);
        leanh::lean_dec(v_n_1061_);
        leanh::lean_dec(v___x_1064_);
        v___x_1066_ = lean_float_array_fget(v_as_1050_, v___x_1065_);
        leanh::lean_dec(v___x_1065_);
        leanh::lean_dec_ref(v_as_1050_);
        v___x_1067_ = leanh::lean_box_float(v___x_1066_);
        v___x_1068_ = leanh::lean_apply_2(v_f_1051_, v___x_1067_, v_b_1053_);
        v___x_1069_ = leanh::lean_apply_4(
            v_toBind_1055_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1068_,
            v___f_1062_,
        );
        return v___x_1069_;
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___lam__0(
    mut v_toPure_1070_: *mut leanh::LeanObject,
    mut v_inst_1071_: *mut leanh::LeanObject,
    mut v_as_1072_: *mut leanh::LeanObject,
    mut v_f_1073_: *mut leanh::LeanObject,
    mut v_n_1074_: *mut leanh::LeanObject,
    mut v_____do__lift_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1075_) == 0 {
        let mut v_a_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_1073_);
        leanh::lean_dec_ref(v_as_1072_);
        leanh::lean_dec_ref(v_inst_1071_);
        v_a_1076_ = leanh::lean_ctor_get(v_____do__lift_1075_, 0);
        leanh::lean_inc(v_a_1076_);
        leanh::lean_dec_ref_known(v_____do__lift_1075_, 1);
        v___x_1077_ =
            leanh::lean_apply_2(v_toPure_1070_, leanh::lean_box(0), v_a_1076_);
        return v___x_1077_;
    } else {
        let mut v_a_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1070_);
        v_a_1078_ = leanh::lean_ctor_get(v_____do__lift_1075_, 0);
        leanh::lean_inc(v_a_1078_);
        leanh::lean_dec_ref_known(v_____do__lift_1075_, 1);
        v___x_1079_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(
            v_inst_1071_,
            v_as_1072_,
            v_f_1073_,
            v_n_1074_,
            v_a_1078_,
        );
        return v___x_1079_;
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg___boxed(
    mut v_inst_1080_: *mut leanh::LeanObject,
    mut v_as_1081_: *mut leanh::LeanObject,
    mut v_f_1082_: *mut leanh::LeanObject,
    mut v_i_1083_: *mut leanh::LeanObject,
    mut v_b_1084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1085_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(
        v_inst_1080_,
        v_as_1081_,
        v_f_1082_,
        v_i_1083_,
        v_b_1084_,
    );
    leanh::lean_dec(v_i_1083_);
    return v_res_1085_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(
    mut v_00_u03b2_1086_: *mut leanh::LeanObject,
    mut v_m_1087_: *mut leanh::LeanObject,
    mut v_inst_1088_: *mut leanh::LeanObject,
    mut v_as_1089_: *mut leanh::LeanObject,
    mut v_f_1090_: *mut leanh::LeanObject,
    mut v_i_1091_: *mut leanh::LeanObject,
    mut v_h_1092_: *mut leanh::LeanObject,
    mut v_b_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___redArg(
        v_inst_1088_,
        v_as_1089_,
        v_f_1090_,
        v_i_1091_,
        v_b_1093_,
    );
    return v___x_1094_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop___boxed(
    mut v_00_u03b2_1095_: *mut leanh::LeanObject,
    mut v_m_1096_: *mut leanh::LeanObject,
    mut v_inst_1097_: *mut leanh::LeanObject,
    mut v_as_1098_: *mut leanh::LeanObject,
    mut v_f_1099_: *mut leanh::LeanObject,
    mut v_i_1100_: *mut leanh::LeanObject,
    mut v_h_1101_: *mut leanh::LeanObject,
    mut v_b_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forIn_loop(
        v_00_u03b2_1095_,
        v_m_1096_,
        v_inst_1097_,
        v_as_1098_,
        v_f_1099_,
        v_i_1100_,
        v_h_1101_,
        v_b_1102_,
    );
    leanh::lean_dec(v_i_1100_);
    return v_res_1103_;
}
pub unsafe fn l_FloatArray_instForInFloatOfMonad___redArg___lam__0(
    mut v_inst_1104_: *mut leanh::LeanObject,
    mut v_00_u03b2_1105_: *mut leanh::LeanObject,
    mut v___y_1106_: *mut leanh::LeanObject,
    mut v___y_1107_: *mut leanh::LeanObject,
    mut v___y_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1109_: usize = 0;
    let mut v___x_1110_: usize = 0;
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1109_ = lean_sarray_size(v___y_1106_);
    v___x_1110_ = 0usize;
    v___x_1111_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_forInUnsafe_loop___redArg(
        v_inst_1104_,
        v___y_1106_,
        v___y_1108_,
        v_sz_1109_,
        v___x_1110_,
        v___y_1107_,
    );
    return v___x_1111_;
}
pub unsafe fn l_FloatArray_instForInFloatOfMonad___redArg(
    mut v_inst_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1113_ = leanh::lean_alloc_closure(
        l_FloatArray_instForInFloatOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1113_, 0, v_inst_1112_);
    return v___f_1113_;
}
pub unsafe fn l_FloatArray_instForInFloatOfMonad(
    mut v_m_1114_: *mut leanh::LeanObject,
    mut v_inst_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1116_ = leanh::lean_alloc_closure(
        l_FloatArray_instForInFloatOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_1116_, 0, v_inst_1115_);
    return v___f_1116_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed(
    mut v_i_1117_: *mut leanh::LeanObject,
    mut v_inst_1118_: *mut leanh::LeanObject,
    mut v_f_1119_: *mut leanh::LeanObject,
    mut v_as_1120_: *mut leanh::LeanObject,
    mut v_stop_1121_: *mut leanh::LeanObject,
    mut v_____do__lift_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1123_: usize = 0;
    let mut v_stop_boxed_1124_: usize = 0;
    let mut v_res_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1123_ = leanh::lean_unbox_usize(v_i_1117_);
    leanh::lean_dec(v_i_1117_);
    v_stop_boxed_1124_ = leanh::lean_unbox_usize(v_stop_1121_);
    leanh::lean_dec(v_stop_1121_);
    v_res_1125_ =
        l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(
            v_i_boxed_1123_,
            v_inst_1118_,
            v_f_1119_,
            v_as_1120_,
            v_stop_boxed_1124_,
            v_____do__lift_1122_,
        );
    return v_res_1125_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
    mut v_inst_1126_: *mut leanh::LeanObject,
    mut v_f_1127_: *mut leanh::LeanObject,
    mut v_as_1128_: *mut leanh::LeanObject,
    mut v_i_1129_: usize,
    mut v_stop_1130_: usize,
    mut v_b_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1132_: u8 = 0;
    v___x_1132_ = lean_usize_dec_eq(v_i_1129_, v_stop_1130_);
    if v___x_1132_ == 0 {
        let mut v_toBind_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: f64 = 0.0;
        let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1133_ = leanh::lean_ctor_get(v_inst_1126_, 1);
        leanh::lean_inc(v_toBind_1133_);
        v___x_1134_ = leanh::lean_box_usize(v_i_1129_);
        v___x_1135_ = leanh::lean_box_usize(v_stop_1130_);
        leanh::lean_inc_ref(v_as_1128_);
        leanh::lean_inc(v_f_1127_);
        v___f_1136_ = leanh::lean_alloc_closure(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        leanh::lean_closure_set(v___f_1136_, 0, v___x_1134_);
        leanh::lean_closure_set(v___f_1136_, 1, v_inst_1126_);
        leanh::lean_closure_set(v___f_1136_, 2, v_f_1127_);
        leanh::lean_closure_set(v___f_1136_, 3, v_as_1128_);
        leanh::lean_closure_set(v___f_1136_, 4, v___x_1135_);
        v___x_1137_ = lean_float_array_uget(v_as_1128_, v_i_1129_);
        leanh::lean_dec_ref(v_as_1128_);
        v___x_1138_ = leanh::lean_box_float(v___x_1137_);
        v___x_1139_ = leanh::lean_apply_2(v_f_1127_, v_b_1131_, v___x_1138_);
        v___x_1140_ = leanh::lean_apply_4(
            v_toBind_1133_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1139_,
            v___f_1136_,
        );
        return v___x_1140_;
    } else {
        let mut v_toApplicative_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_as_1128_);
        leanh::lean_dec(v_f_1127_);
        v_toApplicative_1141_ = leanh::lean_ctor_get(v_inst_1126_, 0);
        leanh::lean_inc_ref(v_toApplicative_1141_);
        leanh::lean_dec_ref(v_inst_1126_);
        v_toPure_1142_ = leanh::lean_ctor_get(v_toApplicative_1141_, 1);
        leanh::lean_inc(v_toPure_1142_);
        leanh::lean_dec_ref(v_toApplicative_1141_);
        v___x_1143_ =
            leanh::lean_apply_2(v_toPure_1142_, leanh::lean_box(0), v_b_1131_);
        return v___x_1143_;
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___lam__0(
    mut v_i_1144_: usize,
    mut v_inst_1145_: *mut leanh::LeanObject,
    mut v_f_1146_: *mut leanh::LeanObject,
    mut v_as_1147_: *mut leanh::LeanObject,
    mut v_stop_1148_: usize,
    mut v_____do__lift_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1150_: usize = 0;
    let mut v___x_1151_: usize = 0;
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = 1usize;
    v___x_1151_ = lean_usize_add(v_i_1144_, v___x_1150_);
    v___x_1152_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
        v_inst_1145_,
        v_f_1146_,
        v_as_1147_,
        v___x_1151_,
        v_stop_1148_,
        v_____do__lift_1149_,
    );
    return v___x_1152_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg___boxed(
    mut v_inst_1153_: *mut leanh::LeanObject,
    mut v_f_1154_: *mut leanh::LeanObject,
    mut v_as_1155_: *mut leanh::LeanObject,
    mut v_i_1156_: *mut leanh::LeanObject,
    mut v_stop_1157_: *mut leanh::LeanObject,
    mut v_b_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1159_: usize = 0;
    let mut v_stop_boxed_1160_: usize = 0;
    let mut v_res_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1159_ = leanh::lean_unbox_usize(v_i_1156_);
    leanh::lean_dec(v_i_1156_);
    v_stop_boxed_1160_ = leanh::lean_unbox_usize(v_stop_1157_);
    leanh::lean_dec(v_stop_1157_);
    v_res_1161_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
        v_inst_1153_,
        v_f_1154_,
        v_as_1155_,
        v_i_boxed_1159_,
        v_stop_boxed_1160_,
        v_b_1158_,
    );
    return v_res_1161_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(
    mut v_00_u03b2_1162_: *mut leanh::LeanObject,
    mut v_m_1163_: *mut leanh::LeanObject,
    mut v_inst_1164_: *mut leanh::LeanObject,
    mut v_f_1165_: *mut leanh::LeanObject,
    mut v_as_1166_: *mut leanh::LeanObject,
    mut v_i_1167_: usize,
    mut v_stop_1168_: usize,
    mut v_b_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1170_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
        v_inst_1164_,
        v_f_1165_,
        v_as_1166_,
        v_i_1167_,
        v_stop_1168_,
        v_b_1169_,
    );
    return v___x_1170_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___boxed(
    mut v_00_u03b2_1171_: *mut leanh::LeanObject,
    mut v_m_1172_: *mut leanh::LeanObject,
    mut v_inst_1173_: *mut leanh::LeanObject,
    mut v_f_1174_: *mut leanh::LeanObject,
    mut v_as_1175_: *mut leanh::LeanObject,
    mut v_i_1176_: *mut leanh::LeanObject,
    mut v_stop_1177_: *mut leanh::LeanObject,
    mut v_b_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1179_: usize = 0;
    let mut v_stop_boxed_1180_: usize = 0;
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1179_ = leanh::lean_unbox_usize(v_i_1176_);
    leanh::lean_dec(v_i_1176_);
    v_stop_boxed_1180_ = leanh::lean_unbox_usize(v_stop_1177_);
    leanh::lean_dec(v_stop_1177_);
    v_res_1181_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold(
        v_00_u03b2_1171_,
        v_m_1172_,
        v_inst_1173_,
        v_f_1174_,
        v_as_1175_,
        v_i_boxed_1179_,
        v_stop_boxed_1180_,
        v_b_1178_,
    );
    return v_res_1181_;
}
pub unsafe fn l_FloatArray_foldlMUnsafe___redArg(
    mut v_inst_1182_: *mut leanh::LeanObject,
    mut v_f_1183_: *mut leanh::LeanObject,
    mut v_init_1184_: *mut leanh::LeanObject,
    mut v_as_1185_: *mut leanh::LeanObject,
    mut v_start_1186_: *mut leanh::LeanObject,
    mut v_stop_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1188_: u8 = 0;
    v___x_1188_ = lean_nat_dec_lt(v_start_1186_, v_stop_1187_);
    if v___x_1188_ == 0 {
        let mut v_toApplicative_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_as_1185_);
        leanh::lean_dec(v_f_1183_);
        v_toApplicative_1189_ = leanh::lean_ctor_get(v_inst_1182_, 0);
        leanh::lean_inc_ref(v_toApplicative_1189_);
        leanh::lean_dec_ref(v_inst_1182_);
        v_toPure_1190_ = leanh::lean_ctor_get(v_toApplicative_1189_, 1);
        leanh::lean_inc(v_toPure_1190_);
        leanh::lean_dec_ref(v_toApplicative_1189_);
        v___x_1191_ =
            leanh::lean_apply_2(v_toPure_1190_, leanh::lean_box(0), v_init_1184_);
        return v___x_1191_;
    } else {
        let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1193_: u8 = 0;
        v___x_1192_ = lean_float_array_size(v_as_1185_);
        v___x_1193_ = lean_nat_dec_le(v_stop_1187_, v___x_1192_);
        if v___x_1193_ == 0 {
            let mut v___x_1194_: u8 = 0;
            v___x_1194_ = lean_nat_dec_lt(v_start_1186_, v___x_1192_);
            if v___x_1194_ == 0 {
                let mut v_toApplicative_1195_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_as_1185_);
                leanh::lean_dec(v_f_1183_);
                v_toApplicative_1195_ = leanh::lean_ctor_get(v_inst_1182_, 0);
                leanh::lean_inc_ref(v_toApplicative_1195_);
                leanh::lean_dec_ref(v_inst_1182_);
                v_toPure_1196_ = leanh::lean_ctor_get(v_toApplicative_1195_, 1);
                leanh::lean_inc(v_toPure_1196_);
                leanh::lean_dec_ref(v_toApplicative_1195_);
                v___x_1197_ = leanh::lean_apply_2(
                    v_toPure_1196_,
                    leanh::lean_box(0),
                    v_init_1184_,
                );
                return v___x_1197_;
            } else {
                let mut v___x_1198_: usize = 0;
                let mut v___x_1199_: usize = 0;
                let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1198_ = lean_usize_of_nat(v_start_1186_);
                v___x_1199_ = lean_usize_of_nat(v___x_1192_);
                v___x_1200_ =
                    l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                        v_inst_1182_,
                        v_f_1183_,
                        v_as_1185_,
                        v___x_1198_,
                        v___x_1199_,
                        v_init_1184_,
                    );
                return v___x_1200_;
            }
        } else {
            let mut v___x_1201_: usize = 0;
            let mut v___x_1202_: usize = 0;
            let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1201_ = lean_usize_of_nat(v_start_1186_);
            v___x_1202_ = lean_usize_of_nat(v_stop_1187_);
            v___x_1203_ =
                l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                    v_inst_1182_,
                    v_f_1183_,
                    v_as_1185_,
                    v___x_1201_,
                    v___x_1202_,
                    v_init_1184_,
                );
            return v___x_1203_;
        }
    }
}
pub unsafe fn l_FloatArray_foldlMUnsafe___redArg___boxed(
    mut v_inst_1204_: *mut leanh::LeanObject,
    mut v_f_1205_: *mut leanh::LeanObject,
    mut v_init_1206_: *mut leanh::LeanObject,
    mut v_as_1207_: *mut leanh::LeanObject,
    mut v_start_1208_: *mut leanh::LeanObject,
    mut v_stop_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1210_ = l_FloatArray_foldlMUnsafe___redArg(
        v_inst_1204_,
        v_f_1205_,
        v_init_1206_,
        v_as_1207_,
        v_start_1208_,
        v_stop_1209_,
    );
    leanh::lean_dec(v_stop_1209_);
    leanh::lean_dec(v_start_1208_);
    return v_res_1210_;
}
pub unsafe fn l_FloatArray_foldlMUnsafe(
    mut v_00_u03b2_1211_: *mut leanh::LeanObject,
    mut v_m_1212_: *mut leanh::LeanObject,
    mut v_inst_1213_: *mut leanh::LeanObject,
    mut v_f_1214_: *mut leanh::LeanObject,
    mut v_init_1215_: *mut leanh::LeanObject,
    mut v_as_1216_: *mut leanh::LeanObject,
    mut v_start_1217_: *mut leanh::LeanObject,
    mut v_stop_1218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1219_: u8 = 0;
    v___x_1219_ = lean_nat_dec_lt(v_start_1217_, v_stop_1218_);
    if v___x_1219_ == 0 {
        let mut v_toApplicative_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_as_1216_);
        leanh::lean_dec(v_f_1214_);
        v_toApplicative_1220_ = leanh::lean_ctor_get(v_inst_1213_, 0);
        leanh::lean_inc_ref(v_toApplicative_1220_);
        leanh::lean_dec_ref(v_inst_1213_);
        v_toPure_1221_ = leanh::lean_ctor_get(v_toApplicative_1220_, 1);
        leanh::lean_inc(v_toPure_1221_);
        leanh::lean_dec_ref(v_toApplicative_1220_);
        v___x_1222_ =
            leanh::lean_apply_2(v_toPure_1221_, leanh::lean_box(0), v_init_1215_);
        return v___x_1222_;
    } else {
        let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: u8 = 0;
        v___x_1223_ = lean_float_array_size(v_as_1216_);
        v___x_1224_ = lean_nat_dec_le(v_stop_1218_, v___x_1223_);
        if v___x_1224_ == 0 {
            let mut v___x_1225_: u8 = 0;
            v___x_1225_ = lean_nat_dec_lt(v_start_1217_, v___x_1223_);
            if v___x_1225_ == 0 {
                let mut v_toApplicative_1226_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_as_1216_);
                leanh::lean_dec(v_f_1214_);
                v_toApplicative_1226_ = leanh::lean_ctor_get(v_inst_1213_, 0);
                leanh::lean_inc_ref(v_toApplicative_1226_);
                leanh::lean_dec_ref(v_inst_1213_);
                v_toPure_1227_ = leanh::lean_ctor_get(v_toApplicative_1226_, 1);
                leanh::lean_inc(v_toPure_1227_);
                leanh::lean_dec_ref(v_toApplicative_1226_);
                v___x_1228_ = leanh::lean_apply_2(
                    v_toPure_1227_,
                    leanh::lean_box(0),
                    v_init_1215_,
                );
                return v___x_1228_;
            } else {
                let mut v___x_1229_: usize = 0;
                let mut v___x_1230_: usize = 0;
                let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1229_ = lean_usize_of_nat(v_start_1217_);
                v___x_1230_ = lean_usize_of_nat(v___x_1223_);
                v___x_1231_ =
                    l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                        v_inst_1213_,
                        v_f_1214_,
                        v_as_1216_,
                        v___x_1229_,
                        v___x_1230_,
                        v_init_1215_,
                    );
                return v___x_1231_;
            }
        } else {
            let mut v___x_1232_: usize = 0;
            let mut v___x_1233_: usize = 0;
            let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1232_ = lean_usize_of_nat(v_start_1217_);
            v___x_1233_ = lean_usize_of_nat(v_stop_1218_);
            v___x_1234_ =
                l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                    v_inst_1213_,
                    v_f_1214_,
                    v_as_1216_,
                    v___x_1232_,
                    v___x_1233_,
                    v_init_1215_,
                );
            return v___x_1234_;
        }
    }
}
pub unsafe fn l_FloatArray_foldlMUnsafe___boxed(
    mut v_00_u03b2_1235_: *mut leanh::LeanObject,
    mut v_m_1236_: *mut leanh::LeanObject,
    mut v_inst_1237_: *mut leanh::LeanObject,
    mut v_f_1238_: *mut leanh::LeanObject,
    mut v_init_1239_: *mut leanh::LeanObject,
    mut v_as_1240_: *mut leanh::LeanObject,
    mut v_start_1241_: *mut leanh::LeanObject,
    mut v_stop_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_FloatArray_foldlMUnsafe(
        v_00_u03b2_1235_,
        v_m_1236_,
        v_inst_1237_,
        v_f_1238_,
        v_init_1239_,
        v_as_1240_,
        v_start_1241_,
        v_stop_1242_,
    );
    leanh::lean_dec(v_stop_1242_);
    leanh::lean_dec(v_start_1241_);
    return v_res_1243_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed(
    mut v_j_1244_: *mut leanh::LeanObject,
    mut v_inst_1245_: *mut leanh::LeanObject,
    mut v_f_1246_: *mut leanh::LeanObject,
    mut v_as_1247_: *mut leanh::LeanObject,
    mut v_stop_1248_: *mut leanh::LeanObject,
    mut v_n_1249_: *mut leanh::LeanObject,
    mut v_____do__lift_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ =
        l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(
            v_j_1244_,
            v_inst_1245_,
            v_f_1246_,
            v_as_1247_,
            v_stop_1248_,
            v_n_1249_,
            v_____do__lift_1250_,
        );
    leanh::lean_dec(v_n_1249_);
    leanh::lean_dec(v_j_1244_);
    return v_res_1251_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(
    mut v_inst_1252_: *mut leanh::LeanObject,
    mut v_f_1253_: *mut leanh::LeanObject,
    mut v_as_1254_: *mut leanh::LeanObject,
    mut v_stop_1255_: *mut leanh::LeanObject,
    mut v_i_1256_: *mut leanh::LeanObject,
    mut v_j_1257_: *mut leanh::LeanObject,
    mut v_b_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1259_: u8 = 0;
    v___x_1259_ = lean_nat_dec_lt(v_j_1257_, v_stop_1255_);
    if v___x_1259_ == 0 {
        let mut v_toApplicative_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_j_1257_);
        leanh::lean_dec(v_stop_1255_);
        leanh::lean_dec_ref(v_as_1254_);
        leanh::lean_dec(v_f_1253_);
        v_toApplicative_1260_ = leanh::lean_ctor_get(v_inst_1252_, 0);
        leanh::lean_inc_ref(v_toApplicative_1260_);
        leanh::lean_dec_ref(v_inst_1252_);
        v_toPure_1261_ = leanh::lean_ctor_get(v_toApplicative_1260_, 1);
        leanh::lean_inc(v_toPure_1261_);
        leanh::lean_dec_ref(v_toApplicative_1260_);
        v___x_1262_ =
            leanh::lean_apply_2(v_toPure_1261_, leanh::lean_box(0), v_b_1258_);
        return v___x_1262_;
    } else {
        let mut v_zero_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1264_: u8 = 0;
        v_zero_1263_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_1264_ = lean_nat_dec_eq(v_i_1256_, v_zero_1263_);
        if v_isZero_1264_ == 1 {
            let mut v_toApplicative_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_j_1257_);
            leanh::lean_dec(v_stop_1255_);
            leanh::lean_dec_ref(v_as_1254_);
            leanh::lean_dec(v_f_1253_);
            v_toApplicative_1265_ = leanh::lean_ctor_get(v_inst_1252_, 0);
            leanh::lean_inc_ref(v_toApplicative_1265_);
            leanh::lean_dec_ref(v_inst_1252_);
            v_toPure_1266_ = leanh::lean_ctor_get(v_toApplicative_1265_, 1);
            leanh::lean_inc(v_toPure_1266_);
            leanh::lean_dec_ref(v_toApplicative_1265_);
            v___x_1267_ =
                leanh::lean_apply_2(v_toPure_1266_, leanh::lean_box(0), v_b_1258_);
            return v___x_1267_;
        } else {
            let mut v_toBind_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1272_: f64 = 0.0;
            let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toBind_1268_ = leanh::lean_ctor_get(v_inst_1252_, 1);
            leanh::lean_inc(v_toBind_1268_);
            v_one_1269_ = leanh::lean_unsigned_to_nat(1);
            v_n_1270_ = lean_nat_sub(v_i_1256_, v_one_1269_);
            leanh::lean_inc_ref(v_as_1254_);
            leanh::lean_inc(v_f_1253_);
            leanh::lean_inc(v_j_1257_);
            v___f_1271_ = leanh::lean_alloc_closure(l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 6);
            leanh::lean_closure_set(v___f_1271_, 0, v_j_1257_);
            leanh::lean_closure_set(v___f_1271_, 1, v_inst_1252_);
            leanh::lean_closure_set(v___f_1271_, 2, v_f_1253_);
            leanh::lean_closure_set(v___f_1271_, 3, v_as_1254_);
            leanh::lean_closure_set(v___f_1271_, 4, v_stop_1255_);
            leanh::lean_closure_set(v___f_1271_, 5, v_n_1270_);
            v___x_1272_ = lean_float_array_fget(v_as_1254_, v_j_1257_);
            leanh::lean_dec(v_j_1257_);
            leanh::lean_dec_ref(v_as_1254_);
            v___x_1273_ = leanh::lean_box_float(v___x_1272_);
            v___x_1274_ = leanh::lean_apply_2(v_f_1253_, v_b_1258_, v___x_1273_);
            v___x_1275_ = leanh::lean_apply_4(
                v_toBind_1268_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_1274_,
                v___f_1271_,
            );
            return v___x_1275_;
        }
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___lam__0(
    mut v_j_1276_: *mut leanh::LeanObject,
    mut v_inst_1277_: *mut leanh::LeanObject,
    mut v_f_1278_: *mut leanh::LeanObject,
    mut v_as_1279_: *mut leanh::LeanObject,
    mut v_stop_1280_: *mut leanh::LeanObject,
    mut v_n_1281_: *mut leanh::LeanObject,
    mut v_____do__lift_1282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = leanh::lean_unsigned_to_nat(1);
    v___x_1284_ = lean_nat_add(v_j_1276_, v___x_1283_);
    v___x_1285_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(
        v_inst_1277_,
        v_f_1278_,
        v_as_1279_,
        v_stop_1280_,
        v_n_1281_,
        v___x_1284_,
        v_____do__lift_1282_,
    );
    return v___x_1285_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg___boxed(
    mut v_inst_1286_: *mut leanh::LeanObject,
    mut v_f_1287_: *mut leanh::LeanObject,
    mut v_as_1288_: *mut leanh::LeanObject,
    mut v_stop_1289_: *mut leanh::LeanObject,
    mut v_i_1290_: *mut leanh::LeanObject,
    mut v_j_1291_: *mut leanh::LeanObject,
    mut v_b_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(
        v_inst_1286_,
        v_f_1287_,
        v_as_1288_,
        v_stop_1289_,
        v_i_1290_,
        v_j_1291_,
        v_b_1292_,
    );
    leanh::lean_dec(v_i_1290_);
    return v_res_1293_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(
    mut v_00_u03b2_1294_: *mut leanh::LeanObject,
    mut v_m_1295_: *mut leanh::LeanObject,
    mut v_inst_1296_: *mut leanh::LeanObject,
    mut v_f_1297_: *mut leanh::LeanObject,
    mut v_as_1298_: *mut leanh::LeanObject,
    mut v_stop_1299_: *mut leanh::LeanObject,
    mut v_h_1300_: *mut leanh::LeanObject,
    mut v_i_1301_: *mut leanh::LeanObject,
    mut v_j_1302_: *mut leanh::LeanObject,
    mut v_b_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___redArg(
        v_inst_1296_,
        v_f_1297_,
        v_as_1298_,
        v_stop_1299_,
        v_i_1301_,
        v_j_1302_,
        v_b_1303_,
    );
    return v___x_1304_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop___boxed(
    mut v_00_u03b2_1305_: *mut leanh::LeanObject,
    mut v_m_1306_: *mut leanh::LeanObject,
    mut v_inst_1307_: *mut leanh::LeanObject,
    mut v_f_1308_: *mut leanh::LeanObject,
    mut v_as_1309_: *mut leanh::LeanObject,
    mut v_stop_1310_: *mut leanh::LeanObject,
    mut v_h_1311_: *mut leanh::LeanObject,
    mut v_i_1312_: *mut leanh::LeanObject,
    mut v_j_1313_: *mut leanh::LeanObject,
    mut v_b_1314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1315_ = l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlM_loop(
        v_00_u03b2_1305_,
        v_m_1306_,
        v_inst_1307_,
        v_f_1308_,
        v_as_1309_,
        v_stop_1310_,
        v_h_1311_,
        v_i_1312_,
        v_j_1313_,
        v_b_1314_,
    );
    leanh::lean_dec(v_i_1312_);
    return v_res_1315_;
}
pub unsafe fn l_FloatArray_foldl___redArg___lam__0(
    mut v_f_1316_: *mut leanh::LeanObject,
    mut v_x1_1317_: *mut leanh::LeanObject,
    mut v_x2_1318_: f64,
) -> *mut leanh::LeanObject {
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ = leanh::lean_box_float(v_x2_1318_);
    v___x_1320_ = leanh::lean_apply_2(v_f_1316_, v_x1_1317_, v___x_1319_);
    return v___x_1320_;
}
pub unsafe fn l_FloatArray_foldl___redArg___lam__0___boxed(
    mut v_f_1321_: *mut leanh::LeanObject,
    mut v_x1_1322_: *mut leanh::LeanObject,
    mut v_x2_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x2_190__boxed_1324_: f64 = 0.0;
    let mut v_res_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x2_190__boxed_1324_ = leanh::lean_unbox_float(v_x2_1323_);
    leanh::lean_dec_ref(v_x2_1323_);
    v_res_1325_ =
        l_FloatArray_foldl___redArg___lam__0(v_f_1321_, v_x1_1322_, v_x2_190__boxed_1324_);
    return v_res_1325_;
}
pub unsafe fn l_FloatArray_foldl___redArg(
    mut v_f_1345_: *mut leanh::LeanObject,
    mut v_init_1346_: *mut leanh::LeanObject,
    mut v_as_1347_: *mut leanh::LeanObject,
    mut v_start_1348_: *mut leanh::LeanObject,
    mut v_stop_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    v___x_1350_ = l_FloatArray_foldl___redArg___closed__9;
    v___x_1351_ = lean_nat_dec_lt(v_start_1348_, v_stop_1349_);
    if v___x_1351_ == 0 {
        leanh::lean_dec_ref(v_as_1347_);
        leanh::lean_dec(v_f_1345_);
        return v_init_1346_;
    } else {
        let mut v___f_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: u8 = 0;
        v___f_1352_ = leanh::lean_alloc_closure(
            l_FloatArray_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1352_, 0, v_f_1345_);
        v___x_1353_ = lean_float_array_size(v_as_1347_);
        v___x_1354_ = lean_nat_dec_le(v_stop_1349_, v___x_1353_);
        if v___x_1354_ == 0 {
            let mut v___x_1355_: u8 = 0;
            v___x_1355_ = lean_nat_dec_lt(v_start_1348_, v___x_1353_);
            if v___x_1355_ == 0 {
                leanh::lean_dec_ref(v___f_1352_);
                leanh::lean_dec_ref(v_as_1347_);
                return v_init_1346_;
            } else {
                let mut v___x_1356_: usize = 0;
                let mut v___x_1357_: usize = 0;
                let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1356_ = lean_usize_of_nat(v_start_1348_);
                v___x_1357_ = lean_usize_of_nat(v___x_1353_);
                v___x_1358_ =
                    l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                        v___x_1350_,
                        v___f_1352_,
                        v_as_1347_,
                        v___x_1356_,
                        v___x_1357_,
                        v_init_1346_,
                    );
                return v___x_1358_;
            }
        } else {
            let mut v___x_1359_: usize = 0;
            let mut v___x_1360_: usize = 0;
            let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1359_ = lean_usize_of_nat(v_start_1348_);
            v___x_1360_ = lean_usize_of_nat(v_stop_1349_);
            v___x_1361_ =
                l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                    v___x_1350_,
                    v___f_1352_,
                    v_as_1347_,
                    v___x_1359_,
                    v___x_1360_,
                    v_init_1346_,
                );
            return v___x_1361_;
        }
    }
}
pub unsafe fn l_FloatArray_foldl___redArg___boxed(
    mut v_f_1362_: *mut leanh::LeanObject,
    mut v_init_1363_: *mut leanh::LeanObject,
    mut v_as_1364_: *mut leanh::LeanObject,
    mut v_start_1365_: *mut leanh::LeanObject,
    mut v_stop_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_FloatArray_foldl___redArg(
        v_f_1362_,
        v_init_1363_,
        v_as_1364_,
        v_start_1365_,
        v_stop_1366_,
    );
    leanh::lean_dec(v_stop_1366_);
    leanh::lean_dec(v_start_1365_);
    return v_res_1367_;
}
pub unsafe fn l_FloatArray_foldl(
    mut v_00_u03b2_1368_: *mut leanh::LeanObject,
    mut v_f_1369_: *mut leanh::LeanObject,
    mut v_init_1370_: *mut leanh::LeanObject,
    mut v_as_1371_: *mut leanh::LeanObject,
    mut v_start_1372_: *mut leanh::LeanObject,
    mut v_stop_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    v___x_1374_ = l_FloatArray_foldl___redArg___closed__9;
    v___x_1375_ = lean_nat_dec_lt(v_start_1372_, v_stop_1373_);
    if v___x_1375_ == 0 {
        leanh::lean_dec_ref(v_as_1371_);
        leanh::lean_dec(v_f_1369_);
        return v_init_1370_;
    } else {
        let mut v___f_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1378_: u8 = 0;
        v___f_1376_ = leanh::lean_alloc_closure(
            l_FloatArray_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_1376_, 0, v_f_1369_);
        v___x_1377_ = lean_float_array_size(v_as_1371_);
        v___x_1378_ = lean_nat_dec_le(v_stop_1373_, v___x_1377_);
        if v___x_1378_ == 0 {
            let mut v___x_1379_: u8 = 0;
            v___x_1379_ = lean_nat_dec_lt(v_start_1372_, v___x_1377_);
            if v___x_1379_ == 0 {
                leanh::lean_dec_ref(v___f_1376_);
                leanh::lean_dec_ref(v_as_1371_);
                return v_init_1370_;
            } else {
                let mut v___x_1380_: usize = 0;
                let mut v___x_1381_: usize = 0;
                let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1380_ = lean_usize_of_nat(v_start_1372_);
                v___x_1381_ = lean_usize_of_nat(v___x_1377_);
                v___x_1382_ =
                    l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                        v___x_1374_,
                        v___f_1376_,
                        v_as_1371_,
                        v___x_1380_,
                        v___x_1381_,
                        v_init_1370_,
                    );
                return v___x_1382_;
            }
        } else {
            let mut v___x_1383_: usize = 0;
            let mut v___x_1384_: usize = 0;
            let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1383_ = lean_usize_of_nat(v_start_1372_);
            v___x_1384_ = lean_usize_of_nat(v_stop_1373_);
            v___x_1385_ =
                l___private_Init_Data_FloatArray_Basic_0__FloatArray_foldlMUnsafe_fold___redArg(
                    v___x_1374_,
                    v___f_1376_,
                    v_as_1371_,
                    v___x_1383_,
                    v___x_1384_,
                    v_init_1370_,
                );
            return v___x_1385_;
        }
    }
}
pub unsafe fn l_FloatArray_foldl___boxed(
    mut v_00_u03b2_1386_: *mut leanh::LeanObject,
    mut v_f_1387_: *mut leanh::LeanObject,
    mut v_init_1388_: *mut leanh::LeanObject,
    mut v_as_1389_: *mut leanh::LeanObject,
    mut v_start_1390_: *mut leanh::LeanObject,
    mut v_stop_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1392_ = l_FloatArray_foldl(
        v_00_u03b2_1386_,
        v_f_1387_,
        v_init_1388_,
        v_as_1389_,
        v_start_1390_,
        v_stop_1391_,
    );
    leanh::lean_dec(v_stop_1391_);
    leanh::lean_dec(v_start_1390_);
    return v_res_1392_;
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(
    mut v_x_1393_: *mut leanh::LeanObject,
    mut v_x_1394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: f64 = 0.0;
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1393_) == 0 {
                    return v_x_1394_;
                } else {
                    v_head_1395_ = leanh::lean_ctor_get(v_x_1393_, 0);
                    v_tail_1396_ = leanh::lean_ctor_get(v_x_1393_, 1);
                    v___x_1397_ = leanh::lean_unbox_float(v_head_1395_);
                    v___x_1398_ = lean_float_array_push(v_x_1394_, v___x_1397_);
                    v_x_1393_ = v_tail_1396_;
                    v_x_1394_ = v___x_1398_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop___boxed(
    mut v_x_1400_: *mut leanh::LeanObject,
    mut v_x_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1402_ =
        l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_x_1400_, v_x_1401_);
    leanh::lean_dec(v_x_1400_);
    return v_res_1402_;
}
pub unsafe fn l_List_toFloatArray(
    mut v_ds_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l_FloatArray_empty;
    v___x_1405_ =
        l___private_Init_Data_FloatArray_Basic_0__List_toFloatArray_loop(v_ds_1403_, v___x_1404_);
    return v___x_1405_;
}
pub unsafe fn l_List_toFloatArray___boxed(
    mut v_ds_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1407_ = l_List_toFloatArray(v_ds_1406_);
    leanh::lean_dec(v_ds_1406_);
    return v_res_1407_;
}
pub unsafe fn l_instToStringFloatArray___lam__0(
    mut v___x_1408_: *mut leanh::LeanObject,
    mut v_ds_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = l_FloatArray_toList(v_ds_1409_);
    v___x_1411_ = l_List_toString___redArg(v___x_1408_, v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn l_instToStringFloatArray___lam__0___boxed(
    mut v___x_1412_: *mut leanh::LeanObject,
    mut v_ds_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_instToStringFloatArray___lam__0(v___x_1412_, v_ds_1413_);
    leanh::lean_dec_ref(v_ds_1413_);
    return v_res_1414_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_FloatArray_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_FloatArray_empty = _init_l_FloatArray_empty();
    leanh::lean_mark_persistent(l_FloatArray_empty);
    l_FloatArray_instInhabited = _init_l_FloatArray_instInhabited();
    leanh::lean_mark_persistent(l_FloatArray_instInhabited);
    l_FloatArray_instEmptyCollection = _init_l_FloatArray_instEmptyCollection();
    leanh::lean_mark_persistent(l_FloatArray_instEmptyCollection);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_FloatArray_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_FloatArray_get___auto__1 = _init_l_FloatArray_get___auto__1();
    leanh::lean_mark_persistent(l_FloatArray_get___auto__1);
    l_FloatArray_uset___auto__1 = _init_l_FloatArray_uset___auto__1();
    leanh::lean_mark_persistent(l_FloatArray_uset___auto__1);
    l_FloatArray_set___auto__1 = _init_l_FloatArray_set___auto__1();
    leanh::lean_mark_persistent(l_FloatArray_set___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_FloatArray_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Float(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_FloatArray_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_FloatArray_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_FloatArray_Basic(builtin);
}