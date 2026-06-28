// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.OrderInsts
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue, l_Lean_Meta_Sym_sym_debug,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox,
};
pub static l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value: LeanStringObject<
    14,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        76, 97, 119, 102, 117, 108, 79, 114, 100, 101, 114, 76, 84, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__1_value
            ) as *mut LeanObject,
            8223326317207303805 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3_value: LeanStringObject<
    82,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 82,
    m_capacity: 82,
    m_length: 81,
    m_data: [
        116, 121, 112, 101, 32, 104, 97, 115, 32, 96, 76, 69, 96, 32, 97, 110, 100, 32, 96, 76, 84,
        96, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 96, 76, 84, 96, 32, 105, 110, 115, 116,
        97, 110, 99, 101, 32, 105, 115, 32, 110, 111, 116, 32, 108, 97, 119, 102, 117, 108, 44, 32,
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122,
        101, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [73, 115, 80, 114, 101, 111, 114, 100, 101, 114, 0],
    };
static mut l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value
            ) as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__0_value)
                as *mut LeanObject,
            10086449716222809528 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2_value: LeanStringObject<59> =
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
            116, 121, 112, 101, 32, 104, 97, 115, 32, 96, 76, 69, 96, 44, 32, 98, 117, 116, 32,
            105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 101, 111, 114, 100, 101, 114, 44,
            32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115,
            105, 122, 101, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value: LeanStringObject<
    15,
> = LeanStringObject {
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
        73, 115, 80, 97, 114, 116, 105, 97, 108, 79, 114, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value: LeanCtorObject<
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
            l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        4001367496390366404 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2_value: LeanStringObject<
    64,
> = LeanStringObject {
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
        116, 121, 112, 101, 32, 104, 97, 115, 32, 96, 76, 69, 96, 44, 32, 98, 117, 116, 32, 105,
        115, 32, 110, 111, 116, 32, 97, 32, 112, 97, 114, 116, 105, 97, 108, 32, 111, 114, 100,
        101, 114, 44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104,
        101, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value: LeanStringObject<
    14,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        73, 115, 76, 105, 110, 101, 97, 114, 79, 114, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__0_value
            ) as *mut LeanObject,
            8214319525129147247 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2_value: LeanStringObject<
    63,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        116, 121, 112, 101, 32, 104, 97, 115, 32, 96, 76, 69, 96, 44, 32, 98, 117, 116, 32, 105,
        115, 32, 110, 111, 116, 32, 97, 32, 108, 105, 110, 101, 97, 114, 32, 111, 114, 100, 101,
        114, 44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101,
        115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value:
    LeanStringObject<17> = LeanStringObject {
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
        73, 115, 76, 105, 110, 101, 97, 114, 80, 114, 101, 111, 114, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value: LeanCtorObject<
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
            l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        14289129126467166869 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2_value:
    LeanStringObject<66> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 66,
    m_capacity: 66,
    m_length: 65,
    m_data: [
        116, 121, 112, 101, 32, 104, 97, 115, 32, 96, 76, 69, 96, 44, 32, 98, 117, 116, 32, 105,
        115, 32, 110, 111, 116, 32, 97, 32, 108, 105, 110, 101, 97, 114, 32, 112, 114, 101, 111,
        114, 100, 101, 114, 44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110,
        116, 104, 101, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(
    mut v_opts_520_: *mut LeanObject,
    mut v_opt_521_: *mut LeanObject,
) -> u8 {
    let mut v_name_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    v_name_522_ = lean_ctor_get(v_opt_521_, 0);
    v_defValue_523_ = lean_ctor_get(v_opt_521_, 1);
    v_map_524_ = lean_ctor_get(v_opts_520_, 0);
    v___x_525_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_524_,
            v_name_522_,
        );
    if lean_obj_tag(v___x_525_) == 0 {
        let mut v___x_526_: u8 = 0;
        v___x_526_ = (lean_unbox(v_defValue_523_) as u8);
        return v___x_526_;
    } else {
        let mut v_val_527_: *mut LeanObject = core::ptr::null_mut();
        v_val_527_ = lean_ctor_get(v___x_525_, 0);
        lean_inc(v_val_527_);
        lean_dec_ref_known(v___x_525_, 1);
        if lean_obj_tag(v_val_527_) == 1 {
            let mut v_v_528_: u8 = 0;
            v_v_528_ = lean_ctor_get_uint8(v_val_527_, 0 as u32);
            lean_dec_ref_known(v_val_527_, 0);
            return v_v_528_;
        } else {
            let mut v___x_529_: u8 = 0;
            lean_dec(v_val_527_);
            v___x_529_ = (lean_unbox(v_defValue_523_) as u8);
            return v___x_529_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0___boxed(
    mut v_opts_530_: *mut LeanObject,
    mut v_opt_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_532_: u8 = 0;
    let mut v_r_533_: *mut LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(
        v_opts_530_,
        v_opt_531_,
    );
    lean_dec_ref(v_opt_531_);
    lean_dec_ref(v_opts_530_);
    v_r_533_ = lean_box((v_res_532_) as usize);
    return v_r_533_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__3;
    v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
    return v___x_541_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(
    mut v_u_542_: *mut LeanObject,
    mut v_type_543_: *mut LeanObject,
    mut v_ltInst_x3f_544_: *mut LeanObject,
    mut v_leInst_x3f_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
    mut v_a_547_: *mut LeanObject,
    mut v_a_548_: *mut LeanObject,
    mut v_a_549_: *mut LeanObject,
    mut v_a_550_: *mut LeanObject,
    mut v_a_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTType_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: u8 = 0;
    let mut v_options_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_579_: u8 = 0;
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_583_: u8 = 0;
    let mut v_a_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_591_: u8 = 0;
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_unused_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ltInst_x3f_544_) == 1 {
                    if lean_obj_tag(v_leInst_x3f_545_) == 1 {
                        v_val_556_ = lean_ctor_get(v_ltInst_x3f_544_, 0);
                        lean_inc(v_val_556_);
                        lean_dec_ref_known(v_ltInst_x3f_544_, 1);
                        v_val_557_ = lean_ctor_get(v_leInst_x3f_545_, 0);
                        lean_inc(v_val_557_);
                        lean_dec_ref_known(v_leInst_x3f_545_, 1);
                        v___x_558_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__2;
                        v___x_559_ = lean_box(0);
                        v___x_560_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_560_, 0, v_u_542_);
                        lean_ctor_set(v___x_560_, 1, v___x_559_);
                        v___x_561_ = l_Lean_mkConst(v___x_558_, v___x_560_);
                        v_lawfulOrderLTType_562_ =
                            l_Lean_mkApp3(v___x_561_, v_type_543_, v_val_556_, v_val_557_);
                        v___x_563_ = lean_box(0);
                        lean_inc_ref(v_lawfulOrderLTType_562_);
                        v___x_564_ = l_Lean_Meta_synthInstance_x3f(
                            v_lawfulOrderLTType_562_,
                            v___x_563_,
                            v_a_548_,
                            v_a_549_,
                            v_a_550_,
                            v_a_551_,
                        );
                        if lean_obj_tag(v___x_564_) == 0 {
                            v_a_565_ = lean_ctor_get(v___x_564_, 0);
                            lean_inc(v_a_565_);
                            if lean_obj_tag(v_a_565_) == 1 {
                                lean_dec_ref_known(v_a_565_, 1);
                                lean_dec_ref(v_lawfulOrderLTType_562_);
                                return v___x_564_;
                            } else {
                                lean_dec(v_a_565_);
                                lean_dec_ref_known(v___x_564_, 1);
                                v___x_566_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_546_);
                                if lean_obj_tag(v___x_566_) == 0 {
                                    v_a_567_ = lean_ctor_get(v___x_566_, 0);
                                    lean_inc(v_a_567_);
                                    lean_dec_ref_known(v___x_566_, 1);
                                    v___x_568_ = (lean_unbox(v_a_567_) as u8);
                                    lean_dec(v_a_567_);
                                    if v___x_568_ == 0 {
                                        lean_dec_ref(v_lawfulOrderLTType_562_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_options_569_ = lean_ctor_get(v_a_550_, 2);
                                        v___x_570_ = l_Lean_Meta_Sym_sym_debug;
                                        v___x_571_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_569_, v___x_570_);
                                        if v___x_571_ == 0 {
                                            lean_dec_ref(v_lawfulOrderLTType_562_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_572_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4_once), _init_l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___closed__4);
                                            v___x_573_ =
                                                l_Lean_indentExpr(v_lawfulOrderLTType_562_);
                                            v___x_574_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_574_, 0, v___x_572_);
                                            lean_ctor_set(v___x_574_, 1, v___x_573_);
                                            v___x_575_ = l_Lean_Meta_Sym_reportIssue(
                                                v___x_574_, v_a_546_, v_a_547_, v_a_548_, v_a_549_,
                                                v_a_550_, v_a_551_,
                                            );
                                            if lean_obj_tag(v___x_575_) == 0 {
                                                lean_dec_ref_known(v___x_575_, 1);
                                                state = 1;
                                                continue;
                                            } else {
                                                v_a_576_ = lean_ctor_get(v___x_575_, 0);
                                                v_isSharedCheck_583_ =
                                                    (!lean_is_exclusive(v___x_575_)) as u8;
                                                if v_isSharedCheck_583_ == 0 {
                                                    v___x_578_ = v___x_575_;
                                                    v_isShared_579_ = v_isSharedCheck_583_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_576_);
                                                    lean_dec(v___x_575_);
                                                    v___x_578_ = lean_box(0);
                                                    v_isShared_579_ = v_isSharedCheck_583_;
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_lawfulOrderLTType_562_);
                                    v_a_584_ = lean_ctor_get(v___x_566_, 0);
                                    v_isSharedCheck_591_ = (!lean_is_exclusive(v___x_566_)) as u8;
                                    if v_isSharedCheck_591_ == 0 {
                                        v___x_586_ = v___x_566_;
                                        v_isShared_587_ = v_isSharedCheck_591_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_584_);
                                        lean_dec(v___x_566_);
                                        v___x_586_ = lean_box(0);
                                        v_isShared_587_ = v_isSharedCheck_591_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_lawfulOrderLTType_562_);
                            return v___x_564_;
                        }
                    } else {
                        lean_dec(v_leInst_x3f_545_);
                        lean_dec_ref(v_type_543_);
                        lean_dec(v_u_542_);
                        v_isSharedCheck_599_ = (!lean_is_exclusive(v_ltInst_x3f_544_)) as u8;
                        if v_isSharedCheck_599_ == 0 {
                            v_unused_600_ = lean_ctor_get(v_ltInst_x3f_544_, 0);
                            lean_dec(v_unused_600_);
                            v___x_593_ = v_ltInst_x3f_544_;
                            v_isShared_594_ = v_isSharedCheck_599_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v_ltInst_x3f_544_);
                            v___x_593_ = lean_box(0);
                            v_isShared_594_ = v_isSharedCheck_599_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_leInst_x3f_545_);
                    lean_dec(v_ltInst_x3f_544_);
                    lean_dec_ref(v_type_543_);
                    lean_dec(v_u_542_);
                    v___x_601_ = lean_box(0);
                    v___x_602_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_602_, 0, v___x_601_);
                    return v___x_602_;
                }
            }
            1 => {
                v___x_554_ = lean_box(0);
                v___x_555_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_555_, 0, v___x_554_);
                return v___x_555_;
            }
            2 => {
                if v_isShared_579_ == 0 {
                    v___x_581_ = v___x_578_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
                    v___x_581_ = v_reuseFailAlloc_582_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_581_;
            }
            4 => {
                if v_isShared_587_ == 0 {
                    v___x_589_ = v___x_586_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
                    v___x_589_ = v_reuseFailAlloc_590_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_589_;
            }
            6 => {
                v___x_595_ = lean_box(0);
                if v_isShared_594_ == 0 {
                    lean_ctor_set_tag(v___x_593_, 0);
                    lean_ctor_set(v___x_593_, 0, v___x_595_);
                    v___x_597_ = v___x_593_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
                    v___x_597_ = v_reuseFailAlloc_598_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg___boxed(
    mut v_u_603_: *mut LeanObject,
    mut v_type_604_: *mut LeanObject,
    mut v_ltInst_x3f_605_: *mut LeanObject,
    mut v_leInst_x3f_606_: *mut LeanObject,
    mut v_a_607_: *mut LeanObject,
    mut v_a_608_: *mut LeanObject,
    mut v_a_609_: *mut LeanObject,
    mut v_a_610_: *mut LeanObject,
    mut v_a_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_614_: *mut LeanObject = core::ptr::null_mut();
    v_res_614_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(
        v_u_603_,
        v_type_604_,
        v_ltInst_x3f_605_,
        v_leInst_x3f_606_,
        v_a_607_,
        v_a_608_,
        v_a_609_,
        v_a_610_,
        v_a_611_,
        v_a_612_,
    );
    lean_dec(v_a_612_);
    lean_dec_ref(v_a_611_);
    lean_dec(v_a_610_);
    lean_dec_ref(v_a_609_);
    lean_dec(v_a_608_);
    lean_dec_ref(v_a_607_);
    return v_res_614_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(
    mut v_u_615_: *mut LeanObject,
    mut v_type_616_: *mut LeanObject,
    mut v_ltInst_x3f_617_: *mut LeanObject,
    mut v_leInst_x3f_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
    mut v_a_621_: *mut LeanObject,
    mut v_a_622_: *mut LeanObject,
    mut v_a_623_: *mut LeanObject,
    mut v_a_624_: *mut LeanObject,
    mut v_a_625_: *mut LeanObject,
    mut v_a_626_: *mut LeanObject,
    mut v_a_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___redArg(
        v_u_615_,
        v_type_616_,
        v_ltInst_x3f_617_,
        v_leInst_x3f_618_,
        v_a_623_,
        v_a_624_,
        v_a_625_,
        v_a_626_,
        v_a_627_,
        v_a_628_,
    );
    return v___x_630_;
}
pub unsafe fn l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f___boxed(
    mut v_u_631_: *mut LeanObject,
    mut v_type_632_: *mut LeanObject,
    mut v_ltInst_x3f_633_: *mut LeanObject,
    mut v_leInst_x3f_634_: *mut LeanObject,
    mut v_a_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
    mut v_a_637_: *mut LeanObject,
    mut v_a_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
    mut v_a_641_: *mut LeanObject,
    mut v_a_642_: *mut LeanObject,
    mut v_a_643_: *mut LeanObject,
    mut v_a_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_646_: *mut LeanObject = core::ptr::null_mut();
    v_res_646_ = l_Lean_Meta_Grind_mkLawfulOrderLTInst_x3f(
        v_u_631_,
        v_type_632_,
        v_ltInst_x3f_633_,
        v_leInst_x3f_634_,
        v_a_635_,
        v_a_636_,
        v_a_637_,
        v_a_638_,
        v_a_639_,
        v_a_640_,
        v_a_641_,
        v_a_642_,
        v_a_643_,
        v_a_644_,
    );
    lean_dec(v_a_644_);
    lean_dec_ref(v_a_643_);
    lean_dec(v_a_642_);
    lean_dec_ref(v_a_641_);
    lean_dec(v_a_640_);
    lean_dec_ref(v_a_639_);
    lean_dec(v_a_638_);
    lean_dec_ref(v_a_637_);
    lean_dec(v_a_636_);
    lean_dec(v_a_635_);
    return v_res_646_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3() -> *mut LeanObject
{
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__2;
    v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
    return v___x_653_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(
    mut v_u_654_: *mut LeanObject,
    mut v_type_655_: *mut LeanObject,
    mut v_leInst_x3f_656_: *mut LeanObject,
    mut v_a_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderType_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    let mut v_options_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_a_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_697_: u8 = 0;
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_701_: u8 = 0;
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_leInst_x3f_656_) == 1 {
                    v_val_667_ = lean_ctor_get(v_leInst_x3f_656_, 0);
                    lean_inc(v_val_667_);
                    lean_dec_ref_known(v_leInst_x3f_656_, 1);
                    v___x_668_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__1;
                    v___x_669_ = lean_box(0);
                    v___x_670_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_670_, 0, v_u_654_);
                    lean_ctor_set(v___x_670_, 1, v___x_669_);
                    v___x_671_ = l_Lean_mkConst(v___x_668_, v___x_670_);
                    v_isPreorderType_672_ = l_Lean_mkAppB(v___x_671_, v_type_655_, v_val_667_);
                    v___x_673_ = lean_box(0);
                    lean_inc_ref(v_isPreorderType_672_);
                    v___x_674_ = l_Lean_Meta_synthInstance_x3f(
                        v_isPreorderType_672_,
                        v___x_673_,
                        v_a_659_,
                        v_a_660_,
                        v_a_661_,
                        v_a_662_,
                    );
                    if lean_obj_tag(v___x_674_) == 0 {
                        v_a_675_ = lean_ctor_get(v___x_674_, 0);
                        lean_inc(v_a_675_);
                        if lean_obj_tag(v_a_675_) == 1 {
                            lean_dec_ref_known(v_a_675_, 1);
                            lean_dec_ref(v_isPreorderType_672_);
                            return v___x_674_;
                        } else {
                            lean_dec(v_a_675_);
                            lean_dec_ref_known(v___x_674_, 1);
                            v___x_676_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_657_);
                            if lean_obj_tag(v___x_676_) == 0 {
                                v_a_677_ = lean_ctor_get(v___x_676_, 0);
                                lean_inc(v_a_677_);
                                lean_dec_ref_known(v___x_676_, 1);
                                v___x_678_ = (lean_unbox(v_a_677_) as u8);
                                lean_dec(v_a_677_);
                                if v___x_678_ == 0 {
                                    lean_dec_ref(v_isPreorderType_672_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_options_679_ = lean_ctor_get(v_a_661_, 2);
                                    v___x_680_ = l_Lean_Meta_Sym_sym_debug;
                                    v___x_681_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_679_, v___x_680_);
                                    if v___x_681_ == 0 {
                                        lean_dec_ref(v_isPreorderType_672_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_682_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3_once), _init_l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___closed__3);
                                        v___x_683_ = l_Lean_indentExpr(v_isPreorderType_672_);
                                        v___x_684_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_684_, 0, v___x_682_);
                                        lean_ctor_set(v___x_684_, 1, v___x_683_);
                                        v___x_685_ = l_Lean_Meta_Sym_reportIssue(
                                            v___x_684_, v_a_657_, v_a_658_, v_a_659_, v_a_660_,
                                            v_a_661_, v_a_662_,
                                        );
                                        if lean_obj_tag(v___x_685_) == 0 {
                                            lean_dec_ref_known(v___x_685_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_686_ = lean_ctor_get(v___x_685_, 0);
                                            v_isSharedCheck_693_ =
                                                (!lean_is_exclusive(v___x_685_)) as u8;
                                            if v_isSharedCheck_693_ == 0 {
                                                v___x_688_ = v___x_685_;
                                                v_isShared_689_ = v_isSharedCheck_693_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_686_);
                                                lean_dec(v___x_685_);
                                                v___x_688_ = lean_box(0);
                                                v_isShared_689_ = v_isSharedCheck_693_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_isPreorderType_672_);
                                v_a_694_ = lean_ctor_get(v___x_676_, 0);
                                v_isSharedCheck_701_ = (!lean_is_exclusive(v___x_676_)) as u8;
                                if v_isSharedCheck_701_ == 0 {
                                    v___x_696_ = v___x_676_;
                                    v_isShared_697_ = v_isSharedCheck_701_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_694_);
                                    lean_dec(v___x_676_);
                                    v___x_696_ = lean_box(0);
                                    v_isShared_697_ = v_isSharedCheck_701_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_isPreorderType_672_);
                        return v___x_674_;
                    }
                } else {
                    lean_dec(v_leInst_x3f_656_);
                    lean_dec_ref(v_type_655_);
                    lean_dec(v_u_654_);
                    v___x_702_ = lean_box(0);
                    v___x_703_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_703_, 0, v___x_702_);
                    return v___x_703_;
                }
            }
            1 => {
                v___x_665_ = lean_box(0);
                v___x_666_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_666_, 0, v___x_665_);
                return v___x_666_;
            }
            2 => {
                if v_isShared_689_ == 0 {
                    v___x_691_ = v___x_688_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
                    v___x_691_ = v_reuseFailAlloc_692_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_691_;
            }
            4 => {
                if v_isShared_697_ == 0 {
                    v___x_699_ = v___x_696_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
                    v___x_699_ = v_reuseFailAlloc_700_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg___boxed(
    mut v_u_704_: *mut LeanObject,
    mut v_type_705_: *mut LeanObject,
    mut v_leInst_x3f_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
    mut v_a_708_: *mut LeanObject,
    mut v_a_709_: *mut LeanObject,
    mut v_a_710_: *mut LeanObject,
    mut v_a_711_: *mut LeanObject,
    mut v_a_712_: *mut LeanObject,
    mut v_a_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_714_: *mut LeanObject = core::ptr::null_mut();
    v_res_714_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(
        v_u_704_,
        v_type_705_,
        v_leInst_x3f_706_,
        v_a_707_,
        v_a_708_,
        v_a_709_,
        v_a_710_,
        v_a_711_,
        v_a_712_,
    );
    lean_dec(v_a_712_);
    lean_dec_ref(v_a_711_);
    lean_dec(v_a_710_);
    lean_dec_ref(v_a_709_);
    lean_dec(v_a_708_);
    lean_dec_ref(v_a_707_);
    return v_res_714_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPreorderInst_x3f(
    mut v_u_715_: *mut LeanObject,
    mut v_type_716_: *mut LeanObject,
    mut v_leInst_x3f_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
    mut v_a_719_: *mut LeanObject,
    mut v_a_720_: *mut LeanObject,
    mut v_a_721_: *mut LeanObject,
    mut v_a_722_: *mut LeanObject,
    mut v_a_723_: *mut LeanObject,
    mut v_a_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f___redArg(
        v_u_715_,
        v_type_716_,
        v_leInst_x3f_717_,
        v_a_722_,
        v_a_723_,
        v_a_724_,
        v_a_725_,
        v_a_726_,
        v_a_727_,
    );
    return v___x_729_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPreorderInst_x3f___boxed(
    mut v_u_730_: *mut LeanObject,
    mut v_type_731_: *mut LeanObject,
    mut v_leInst_x3f_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_a_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_744_: *mut LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Lean_Meta_Grind_mkIsPreorderInst_x3f(
        v_u_730_,
        v_type_731_,
        v_leInst_x3f_732_,
        v_a_733_,
        v_a_734_,
        v_a_735_,
        v_a_736_,
        v_a_737_,
        v_a_738_,
        v_a_739_,
        v_a_740_,
        v_a_741_,
        v_a_742_,
    );
    lean_dec(v_a_742_);
    lean_dec_ref(v_a_741_);
    lean_dec(v_a_740_);
    lean_dec_ref(v_a_739_);
    lean_dec(v_a_738_);
    lean_dec_ref(v_a_737_);
    lean_dec(v_a_736_);
    lean_dec_ref(v_a_735_);
    lean_dec(v_a_734_);
    lean_dec(v_a_733_);
    return v_res_744_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__2;
    v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
    return v___x_751_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(
    mut v_u_752_: *mut LeanObject,
    mut v_type_753_: *mut LeanObject,
    mut v_leInst_x3f_754_: *mut LeanObject,
    mut v_a_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
    mut v_a_757_: *mut LeanObject,
    mut v_a_758_: *mut LeanObject,
    mut v_a_759_: *mut LeanObject,
    mut v_a_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPartialOrderType_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    let mut v_options_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u8 = 0;
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut v_a_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_leInst_x3f_754_) == 1 {
                    v_val_765_ = lean_ctor_get(v_leInst_x3f_754_, 0);
                    lean_inc(v_val_765_);
                    lean_dec_ref_known(v_leInst_x3f_754_, 1);
                    v___x_766_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__1;
                    v___x_767_ = lean_box(0);
                    v___x_768_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_768_, 0, v_u_752_);
                    lean_ctor_set(v___x_768_, 1, v___x_767_);
                    v___x_769_ = l_Lean_mkConst(v___x_766_, v___x_768_);
                    v_isPartialOrderType_770_ = l_Lean_mkAppB(v___x_769_, v_type_753_, v_val_765_);
                    v___x_771_ = lean_box(0);
                    lean_inc_ref(v_isPartialOrderType_770_);
                    v___x_772_ = l_Lean_Meta_synthInstance_x3f(
                        v_isPartialOrderType_770_,
                        v___x_771_,
                        v_a_757_,
                        v_a_758_,
                        v_a_759_,
                        v_a_760_,
                    );
                    if lean_obj_tag(v___x_772_) == 0 {
                        v_a_773_ = lean_ctor_get(v___x_772_, 0);
                        lean_inc(v_a_773_);
                        if lean_obj_tag(v_a_773_) == 1 {
                            lean_dec_ref_known(v_a_773_, 1);
                            lean_dec_ref(v_isPartialOrderType_770_);
                            return v___x_772_;
                        } else {
                            lean_dec(v_a_773_);
                            lean_dec_ref_known(v___x_772_, 1);
                            v___x_774_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_755_);
                            if lean_obj_tag(v___x_774_) == 0 {
                                v_a_775_ = lean_ctor_get(v___x_774_, 0);
                                lean_inc(v_a_775_);
                                lean_dec_ref_known(v___x_774_, 1);
                                v___x_776_ = (lean_unbox(v_a_775_) as u8);
                                lean_dec(v_a_775_);
                                if v___x_776_ == 0 {
                                    lean_dec_ref(v_isPartialOrderType_770_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_options_777_ = lean_ctor_get(v_a_759_, 2);
                                    v___x_778_ = l_Lean_Meta_Sym_sym_debug;
                                    v___x_779_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_777_, v___x_778_);
                                    if v___x_779_ == 0 {
                                        lean_dec_ref(v_isPartialOrderType_770_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_780_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3_once), _init_l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___closed__3);
                                        v___x_781_ = l_Lean_indentExpr(v_isPartialOrderType_770_);
                                        v___x_782_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_782_, 0, v___x_780_);
                                        lean_ctor_set(v___x_782_, 1, v___x_781_);
                                        v___x_783_ = l_Lean_Meta_Sym_reportIssue(
                                            v___x_782_, v_a_755_, v_a_756_, v_a_757_, v_a_758_,
                                            v_a_759_, v_a_760_,
                                        );
                                        if lean_obj_tag(v___x_783_) == 0 {
                                            lean_dec_ref_known(v___x_783_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_784_ = lean_ctor_get(v___x_783_, 0);
                                            v_isSharedCheck_791_ =
                                                (!lean_is_exclusive(v___x_783_)) as u8;
                                            if v_isSharedCheck_791_ == 0 {
                                                v___x_786_ = v___x_783_;
                                                v_isShared_787_ = v_isSharedCheck_791_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_784_);
                                                lean_dec(v___x_783_);
                                                v___x_786_ = lean_box(0);
                                                v_isShared_787_ = v_isSharedCheck_791_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_isPartialOrderType_770_);
                                v_a_792_ = lean_ctor_get(v___x_774_, 0);
                                v_isSharedCheck_799_ = (!lean_is_exclusive(v___x_774_)) as u8;
                                if v_isSharedCheck_799_ == 0 {
                                    v___x_794_ = v___x_774_;
                                    v_isShared_795_ = v_isSharedCheck_799_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_792_);
                                    lean_dec(v___x_774_);
                                    v___x_794_ = lean_box(0);
                                    v_isShared_795_ = v_isSharedCheck_799_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_isPartialOrderType_770_);
                        return v___x_772_;
                    }
                } else {
                    lean_dec(v_leInst_x3f_754_);
                    lean_dec_ref(v_type_753_);
                    lean_dec(v_u_752_);
                    v___x_800_ = lean_box(0);
                    v___x_801_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_801_, 0, v___x_800_);
                    return v___x_801_;
                }
            }
            1 => {
                v___x_763_ = lean_box(0);
                v___x_764_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_764_, 0, v___x_763_);
                return v___x_764_;
            }
            2 => {
                if v_isShared_787_ == 0 {
                    v___x_789_ = v___x_786_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
                    v___x_789_ = v_reuseFailAlloc_790_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_789_;
            }
            4 => {
                if v_isShared_795_ == 0 {
                    v___x_797_ = v___x_794_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
                    v___x_797_ = v_reuseFailAlloc_798_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg___boxed(
    mut v_u_802_: *mut LeanObject,
    mut v_type_803_: *mut LeanObject,
    mut v_leInst_x3f_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
    mut v_a_808_: *mut LeanObject,
    mut v_a_809_: *mut LeanObject,
    mut v_a_810_: *mut LeanObject,
    mut v_a_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(
        v_u_802_,
        v_type_803_,
        v_leInst_x3f_804_,
        v_a_805_,
        v_a_806_,
        v_a_807_,
        v_a_808_,
        v_a_809_,
        v_a_810_,
    );
    lean_dec(v_a_810_);
    lean_dec_ref(v_a_809_);
    lean_dec(v_a_808_);
    lean_dec_ref(v_a_807_);
    lean_dec(v_a_806_);
    lean_dec_ref(v_a_805_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(
    mut v_u_813_: *mut LeanObject,
    mut v_type_814_: *mut LeanObject,
    mut v_leInst_x3f_815_: *mut LeanObject,
    mut v_a_816_: *mut LeanObject,
    mut v_a_817_: *mut LeanObject,
    mut v_a_818_: *mut LeanObject,
    mut v_a_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
    mut v_a_823_: *mut LeanObject,
    mut v_a_824_: *mut LeanObject,
    mut v_a_825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    v___x_827_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___redArg(
        v_u_813_,
        v_type_814_,
        v_leInst_x3f_815_,
        v_a_820_,
        v_a_821_,
        v_a_822_,
        v_a_823_,
        v_a_824_,
        v_a_825_,
    );
    return v___x_827_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f___boxed(
    mut v_u_828_: *mut LeanObject,
    mut v_type_829_: *mut LeanObject,
    mut v_leInst_x3f_830_: *mut LeanObject,
    mut v_a_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_a_835_: *mut LeanObject,
    mut v_a_836_: *mut LeanObject,
    mut v_a_837_: *mut LeanObject,
    mut v_a_838_: *mut LeanObject,
    mut v_a_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lean_Meta_Grind_mkIsPartialOrderInst_x3f(
        v_u_828_,
        v_type_829_,
        v_leInst_x3f_830_,
        v_a_831_,
        v_a_832_,
        v_a_833_,
        v_a_834_,
        v_a_835_,
        v_a_836_,
        v_a_837_,
        v_a_838_,
        v_a_839_,
        v_a_840_,
    );
    lean_dec(v_a_840_);
    lean_dec_ref(v_a_839_);
    lean_dec(v_a_838_);
    lean_dec_ref(v_a_837_);
    lean_dec(v_a_836_);
    lean_dec_ref(v_a_835_);
    lean_dec(v_a_834_);
    lean_dec_ref(v_a_833_);
    lean_dec(v_a_832_);
    lean_dec(v_a_831_);
    return v_res_842_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__2;
    v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
    return v___x_849_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(
    mut v_u_850_: *mut LeanObject,
    mut v_type_851_: *mut LeanObject,
    mut v_leInst_x3f_852_: *mut LeanObject,
    mut v_a_853_: *mut LeanObject,
    mut v_a_854_: *mut LeanObject,
    mut v_a_855_: *mut LeanObject,
    mut v_a_856_: *mut LeanObject,
    mut v_a_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearOrderType_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    let mut v_options_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_885_: u8 = 0;
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_889_: u8 = 0;
    let mut v_a_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_leInst_x3f_852_) == 1 {
                    v_val_863_ = lean_ctor_get(v_leInst_x3f_852_, 0);
                    lean_inc(v_val_863_);
                    lean_dec_ref_known(v_leInst_x3f_852_, 1);
                    v___x_864_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__1;
                    v___x_865_ = lean_box(0);
                    v___x_866_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_866_, 0, v_u_850_);
                    lean_ctor_set(v___x_866_, 1, v___x_865_);
                    v___x_867_ = l_Lean_mkConst(v___x_864_, v___x_866_);
                    v_isLinearOrderType_868_ = l_Lean_mkAppB(v___x_867_, v_type_851_, v_val_863_);
                    v___x_869_ = lean_box(0);
                    lean_inc_ref(v_isLinearOrderType_868_);
                    v___x_870_ = l_Lean_Meta_synthInstance_x3f(
                        v_isLinearOrderType_868_,
                        v___x_869_,
                        v_a_855_,
                        v_a_856_,
                        v_a_857_,
                        v_a_858_,
                    );
                    if lean_obj_tag(v___x_870_) == 0 {
                        v_a_871_ = lean_ctor_get(v___x_870_, 0);
                        lean_inc(v_a_871_);
                        if lean_obj_tag(v_a_871_) == 1 {
                            lean_dec_ref_known(v_a_871_, 1);
                            lean_dec_ref(v_isLinearOrderType_868_);
                            return v___x_870_;
                        } else {
                            lean_dec_ref_known(v___x_870_, 1);
                            lean_dec(v_a_871_);
                            v___x_872_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_853_);
                            if lean_obj_tag(v___x_872_) == 0 {
                                v_a_873_ = lean_ctor_get(v___x_872_, 0);
                                lean_inc(v_a_873_);
                                lean_dec_ref_known(v___x_872_, 1);
                                v___x_874_ = (lean_unbox(v_a_873_) as u8);
                                lean_dec(v_a_873_);
                                if v___x_874_ == 0 {
                                    lean_dec_ref(v_isLinearOrderType_868_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_options_875_ = lean_ctor_get(v_a_857_, 2);
                                    v___x_876_ = l_Lean_Meta_Sym_sym_debug;
                                    v___x_877_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_875_, v___x_876_);
                                    if v___x_877_ == 0 {
                                        lean_dec_ref(v_isLinearOrderType_868_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_878_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3_once), _init_l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___closed__3);
                                        v___x_879_ = l_Lean_indentExpr(v_isLinearOrderType_868_);
                                        v___x_880_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_880_, 0, v___x_878_);
                                        lean_ctor_set(v___x_880_, 1, v___x_879_);
                                        v___x_881_ = l_Lean_Meta_Sym_reportIssue(
                                            v___x_880_, v_a_853_, v_a_854_, v_a_855_, v_a_856_,
                                            v_a_857_, v_a_858_,
                                        );
                                        if lean_obj_tag(v___x_881_) == 0 {
                                            lean_dec_ref_known(v___x_881_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_882_ = lean_ctor_get(v___x_881_, 0);
                                            v_isSharedCheck_889_ =
                                                (!lean_is_exclusive(v___x_881_)) as u8;
                                            if v_isSharedCheck_889_ == 0 {
                                                v___x_884_ = v___x_881_;
                                                v_isShared_885_ = v_isSharedCheck_889_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_882_);
                                                lean_dec(v___x_881_);
                                                v___x_884_ = lean_box(0);
                                                v_isShared_885_ = v_isSharedCheck_889_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_isLinearOrderType_868_);
                                v_a_890_ = lean_ctor_get(v___x_872_, 0);
                                v_isSharedCheck_897_ = (!lean_is_exclusive(v___x_872_)) as u8;
                                if v_isSharedCheck_897_ == 0 {
                                    v___x_892_ = v___x_872_;
                                    v_isShared_893_ = v_isSharedCheck_897_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_890_);
                                    lean_dec(v___x_872_);
                                    v___x_892_ = lean_box(0);
                                    v_isShared_893_ = v_isSharedCheck_897_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_isLinearOrderType_868_);
                        return v___x_870_;
                    }
                } else {
                    lean_dec(v_leInst_x3f_852_);
                    lean_dec_ref(v_type_851_);
                    lean_dec(v_u_850_);
                    v___x_898_ = lean_box(0);
                    v___x_899_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_899_, 0, v___x_898_);
                    return v___x_899_;
                }
            }
            1 => {
                v___x_861_ = lean_box(0);
                v___x_862_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_862_, 0, v___x_861_);
                return v___x_862_;
            }
            2 => {
                if v_isShared_885_ == 0 {
                    v___x_887_ = v___x_884_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
                    v___x_887_ = v_reuseFailAlloc_888_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_887_;
            }
            4 => {
                if v_isShared_893_ == 0 {
                    v___x_895_ = v___x_892_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
                    v___x_895_ = v_reuseFailAlloc_896_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg___boxed(
    mut v_u_900_: *mut LeanObject,
    mut v_type_901_: *mut LeanObject,
    mut v_leInst_x3f_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
    mut v_a_904_: *mut LeanObject,
    mut v_a_905_: *mut LeanObject,
    mut v_a_906_: *mut LeanObject,
    mut v_a_907_: *mut LeanObject,
    mut v_a_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_910_: *mut LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(
        v_u_900_,
        v_type_901_,
        v_leInst_x3f_902_,
        v_a_903_,
        v_a_904_,
        v_a_905_,
        v_a_906_,
        v_a_907_,
        v_a_908_,
    );
    lean_dec(v_a_908_);
    lean_dec_ref(v_a_907_);
    lean_dec(v_a_906_);
    lean_dec_ref(v_a_905_);
    lean_dec(v_a_904_);
    lean_dec_ref(v_a_903_);
    return v_res_910_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(
    mut v_u_911_: *mut LeanObject,
    mut v_type_912_: *mut LeanObject,
    mut v_leInst_x3f_913_: *mut LeanObject,
    mut v_a_914_: *mut LeanObject,
    mut v_a_915_: *mut LeanObject,
    mut v_a_916_: *mut LeanObject,
    mut v_a_917_: *mut LeanObject,
    mut v_a_918_: *mut LeanObject,
    mut v_a_919_: *mut LeanObject,
    mut v_a_920_: *mut LeanObject,
    mut v_a_921_: *mut LeanObject,
    mut v_a_922_: *mut LeanObject,
    mut v_a_923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___redArg(
        v_u_911_,
        v_type_912_,
        v_leInst_x3f_913_,
        v_a_918_,
        v_a_919_,
        v_a_920_,
        v_a_921_,
        v_a_922_,
        v_a_923_,
    );
    return v___x_925_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f___boxed(
    mut v_u_926_: *mut LeanObject,
    mut v_type_927_: *mut LeanObject,
    mut v_leInst_x3f_928_: *mut LeanObject,
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
    mut v_a_932_: *mut LeanObject,
    mut v_a_933_: *mut LeanObject,
    mut v_a_934_: *mut LeanObject,
    mut v_a_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
    mut v_a_937_: *mut LeanObject,
    mut v_a_938_: *mut LeanObject,
    mut v_a_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_940_: *mut LeanObject = core::ptr::null_mut();
    v_res_940_ = l_Lean_Meta_Grind_mkIsLinearOrderInst_x3f(
        v_u_926_,
        v_type_927_,
        v_leInst_x3f_928_,
        v_a_929_,
        v_a_930_,
        v_a_931_,
        v_a_932_,
        v_a_933_,
        v_a_934_,
        v_a_935_,
        v_a_936_,
        v_a_937_,
        v_a_938_,
    );
    lean_dec(v_a_938_);
    lean_dec_ref(v_a_937_);
    lean_dec(v_a_936_);
    lean_dec_ref(v_a_935_);
    lean_dec(v_a_934_);
    lean_dec_ref(v_a_933_);
    lean_dec(v_a_932_);
    lean_dec_ref(v_a_931_);
    lean_dec(v_a_930_);
    lean_dec(v_a_929_);
    return v_res_940_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    v___x_946_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__2;
    v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
    return v___x_947_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(
    mut v_u_948_: *mut LeanObject,
    mut v_type_949_: *mut LeanObject,
    mut v_leInst_x3f_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
    mut v_a_955_: *mut LeanObject,
    mut v_a_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearOrderType_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    let mut v_options_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: u8 = 0;
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_983_: u8 = 0;
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_987_: u8 = 0;
    let mut v_a_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_leInst_x3f_950_) == 1 {
                    v_val_961_ = lean_ctor_get(v_leInst_x3f_950_, 0);
                    lean_inc(v_val_961_);
                    lean_dec_ref_known(v_leInst_x3f_950_, 1);
                    v___x_962_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__1;
                    v___x_963_ = lean_box(0);
                    v___x_964_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_964_, 0, v_u_948_);
                    lean_ctor_set(v___x_964_, 1, v___x_963_);
                    v___x_965_ = l_Lean_mkConst(v___x_962_, v___x_964_);
                    v_isLinearOrderType_966_ = l_Lean_mkAppB(v___x_965_, v_type_949_, v_val_961_);
                    v___x_967_ = lean_box(0);
                    lean_inc_ref(v_isLinearOrderType_966_);
                    v___x_968_ = l_Lean_Meta_synthInstance_x3f(
                        v_isLinearOrderType_966_,
                        v___x_967_,
                        v_a_953_,
                        v_a_954_,
                        v_a_955_,
                        v_a_956_,
                    );
                    if lean_obj_tag(v___x_968_) == 0 {
                        v_a_969_ = lean_ctor_get(v___x_968_, 0);
                        lean_inc(v_a_969_);
                        if lean_obj_tag(v_a_969_) == 1 {
                            lean_dec_ref_known(v_a_969_, 1);
                            lean_dec_ref(v_isLinearOrderType_966_);
                            return v___x_968_;
                        } else {
                            lean_dec_ref_known(v___x_968_, 1);
                            lean_dec(v_a_969_);
                            v___x_970_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_951_);
                            if lean_obj_tag(v___x_970_) == 0 {
                                v_a_971_ = lean_ctor_get(v___x_970_, 0);
                                lean_inc(v_a_971_);
                                lean_dec_ref_known(v___x_970_, 1);
                                v___x_972_ = (lean_unbox(v_a_971_) as u8);
                                lean_dec(v_a_971_);
                                if v___x_972_ == 0 {
                                    lean_dec_ref(v_isLinearOrderType_966_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_options_973_ = lean_ctor_get(v_a_955_, 2);
                                    v___x_974_ = l_Lean_Meta_Sym_sym_debug;
                                    v___x_975_ = l_Lean_Option_get___at___00Lean_Meta_Grind_mkLawfulOrderLTInst_x3f_spec__0(v_options_973_, v___x_974_);
                                    if v___x_975_ == 0 {
                                        lean_dec_ref(v_isLinearOrderType_966_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_976_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3_once), _init_l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___closed__3);
                                        v___x_977_ = l_Lean_indentExpr(v_isLinearOrderType_966_);
                                        v___x_978_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_978_, 0, v___x_976_);
                                        lean_ctor_set(v___x_978_, 1, v___x_977_);
                                        v___x_979_ = l_Lean_Meta_Sym_reportIssue(
                                            v___x_978_, v_a_951_, v_a_952_, v_a_953_, v_a_954_,
                                            v_a_955_, v_a_956_,
                                        );
                                        if lean_obj_tag(v___x_979_) == 0 {
                                            lean_dec_ref_known(v___x_979_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_980_ = lean_ctor_get(v___x_979_, 0);
                                            v_isSharedCheck_987_ =
                                                (!lean_is_exclusive(v___x_979_)) as u8;
                                            if v_isSharedCheck_987_ == 0 {
                                                v___x_982_ = v___x_979_;
                                                v_isShared_983_ = v_isSharedCheck_987_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_980_);
                                                lean_dec(v___x_979_);
                                                v___x_982_ = lean_box(0);
                                                v_isShared_983_ = v_isSharedCheck_987_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_isLinearOrderType_966_);
                                v_a_988_ = lean_ctor_get(v___x_970_, 0);
                                v_isSharedCheck_995_ = (!lean_is_exclusive(v___x_970_)) as u8;
                                if v_isSharedCheck_995_ == 0 {
                                    v___x_990_ = v___x_970_;
                                    v_isShared_991_ = v_isSharedCheck_995_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_988_);
                                    lean_dec(v___x_970_);
                                    v___x_990_ = lean_box(0);
                                    v_isShared_991_ = v_isSharedCheck_995_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_isLinearOrderType_966_);
                        return v___x_968_;
                    }
                } else {
                    lean_dec(v_leInst_x3f_950_);
                    lean_dec_ref(v_type_949_);
                    lean_dec(v_u_948_);
                    v___x_996_ = lean_box(0);
                    v___x_997_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_997_, 0, v___x_996_);
                    return v___x_997_;
                }
            }
            1 => {
                v___x_959_ = lean_box(0);
                v___x_960_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_960_, 0, v___x_959_);
                return v___x_960_;
            }
            2 => {
                if v_isShared_983_ == 0 {
                    v___x_985_ = v___x_982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
                    v___x_985_ = v_reuseFailAlloc_986_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_985_;
            }
            4 => {
                if v_isShared_991_ == 0 {
                    v___x_993_ = v___x_990_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
                    v___x_993_ = v_reuseFailAlloc_994_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg___boxed(
    mut v_u_998_: *mut LeanObject,
    mut v_type_999_: *mut LeanObject,
    mut v_leInst_x3f_1000_: *mut LeanObject,
    mut v_a_1001_: *mut LeanObject,
    mut v_a_1002_: *mut LeanObject,
    mut v_a_1003_: *mut LeanObject,
    mut v_a_1004_: *mut LeanObject,
    mut v_a_1005_: *mut LeanObject,
    mut v_a_1006_: *mut LeanObject,
    mut v_a_1007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1008_: *mut LeanObject = core::ptr::null_mut();
    v_res_1008_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(
        v_u_998_,
        v_type_999_,
        v_leInst_x3f_1000_,
        v_a_1001_,
        v_a_1002_,
        v_a_1003_,
        v_a_1004_,
        v_a_1005_,
        v_a_1006_,
    );
    lean_dec(v_a_1006_);
    lean_dec_ref(v_a_1005_);
    lean_dec(v_a_1004_);
    lean_dec_ref(v_a_1003_);
    lean_dec(v_a_1002_);
    lean_dec_ref(v_a_1001_);
    return v_res_1008_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(
    mut v_u_1009_: *mut LeanObject,
    mut v_type_1010_: *mut LeanObject,
    mut v_leInst_x3f_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
    mut v_a_1014_: *mut LeanObject,
    mut v_a_1015_: *mut LeanObject,
    mut v_a_1016_: *mut LeanObject,
    mut v_a_1017_: *mut LeanObject,
    mut v_a_1018_: *mut LeanObject,
    mut v_a_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___redArg(
        v_u_1009_,
        v_type_1010_,
        v_leInst_x3f_1011_,
        v_a_1016_,
        v_a_1017_,
        v_a_1018_,
        v_a_1019_,
        v_a_1020_,
        v_a_1021_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f___boxed(
    mut v_u_1024_: *mut LeanObject,
    mut v_type_1025_: *mut LeanObject,
    mut v_leInst_x3f_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
    mut v_a_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
    mut v_a_1030_: *mut LeanObject,
    mut v_a_1031_: *mut LeanObject,
    mut v_a_1032_: *mut LeanObject,
    mut v_a_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1038_: *mut LeanObject = core::ptr::null_mut();
    v_res_1038_ = l_Lean_Meta_Grind_mkIsLinearPreorderInst_x3f(
        v_u_1024_,
        v_type_1025_,
        v_leInst_x3f_1026_,
        v_a_1027_,
        v_a_1028_,
        v_a_1029_,
        v_a_1030_,
        v_a_1031_,
        v_a_1032_,
        v_a_1033_,
        v_a_1034_,
        v_a_1035_,
        v_a_1036_,
    );
    lean_dec(v_a_1036_);
    lean_dec_ref(v_a_1035_);
    lean_dec(v_a_1034_);
    lean_dec_ref(v_a_1033_);
    lean_dec(v_a_1032_);
    lean_dec_ref(v_a_1031_);
    lean_dec(v_a_1030_);
    lean_dec_ref(v_a_1029_);
    lean_dec(v_a_1028_);
    lean_dec(v_a_1027_);
    return v_res_1038_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_OrderInsts(builtin);
}
