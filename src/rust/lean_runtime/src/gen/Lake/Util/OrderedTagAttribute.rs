// Lean compiler output
// Module: Lake.Util.OrderedTagAttribute
// Imports: Lean.Attributes
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_Attribute_Builtin_ensureNoArgs,
    l_Lean_instBEqAttributeKind_beq, l_Lean_instInhabitedAttributeImpl_default,
    l_Lean_registerBuiltinAttribute, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg, l_Lean_instInhabitedEnvExtension_default,
    l_Lean_instInhabitedPersistentEnvExtensionState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_4, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value:
    LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedOrderedTagAttribute_default___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__3_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedOrderedTagAttribute_default___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedOrderedTagAttribute_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedOrderedTagAttribute: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value: LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__5_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value: LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value: LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value)
        as *mut LeanObject;
static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value: LeanCtorObject<3> =
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
                l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__16_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___auto__1___closed__17_value: LeanStringObject<11> =
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
        m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___auto__1___closed__17_value)
        as *mut LeanObject;
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_registerOrderedTagAttribute___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
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
            116, 97, 103, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 108, 111, 99, 97, 108, 32, 101, 110,
            116, 114, 105, 101, 115, 58, 32, 0,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___lam__1___closed__5_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__1___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___lam__6___closed__0_value: LeanStringObject<13> =
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
        m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__6___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___lam__6___closed__2_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___lam__6___closed__2_value)
        as *mut LeanObject;
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___lam__6___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_registerOrderedTagAttribute___lam__7___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_registerOrderedTagAttribute___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_registerOrderedTagAttribute___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_registerOrderedTagAttribute___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__0_value) as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_registerOrderedTagAttribute___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_registerOrderedTagAttribute___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__1_value) as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_registerOrderedTagAttribute___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_registerOrderedTagAttribute___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__2_value) as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_registerOrderedTagAttribute___lam__3 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_registerOrderedTagAttribute___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__3_value) as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__4_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_registerOrderedTagAttribute___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__4_value) as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_registerOrderedTagAttribute___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__5_value) as *mut LeanObject;
pub static l_Lake_registerOrderedTagAttribute___closed__6_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_registerOrderedTagAttribute___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_registerOrderedTagAttribute___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_registerOrderedTagAttribute___closed__6_value) as *mut LeanObject;
static mut l_Lake_OrderedTagAttribute_hasTag___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_OrderedTagAttribute_hasTag___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_OrderedTagAttribute_getAllEntries___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__0(
    mut v_x_647_: *mut LeanObject,
    mut v___y_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    v___x_650_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___closed__1;
    v___x_651_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_651_, 0, v___x_650_);
    return v___x_651_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__0___boxed(
    mut v_x_652_: *mut LeanObject,
    mut v___y_653_: *mut LeanObject,
    mut v___y_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_655_: *mut LeanObject = core::ptr::null_mut();
    v_res_655_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__0(v_x_652_, v___y_653_);
    lean_dec_ref(v___y_653_);
    lean_dec_ref(v_x_652_);
    return v_res_655_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__1(
    mut v_s_656_: *mut LeanObject,
    mut v_x_657_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_656_);
    return v_s_656_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__1___boxed(
    mut v_s_658_: *mut LeanObject,
    mut v_x_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_660_: *mut LeanObject = core::ptr::null_mut();
    v_res_660_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__1(v_s_658_, v_x_659_);
    lean_dec(v_x_659_);
    lean_dec_ref(v_s_658_);
    return v_res_660_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(
    mut v_x_665_: *mut LeanObject,
    mut v_x_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    v___x_667_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___closed__1;
    return v___x_667_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__2___boxed(
    mut v_x_668_: *mut LeanObject,
    mut v_x_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_670_: *mut LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__2(v_x_668_, v_x_669_);
    lean_dec_ref(v_x_669_);
    lean_dec_ref(v_x_668_);
    return v_res_670_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(
    mut v_x_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    v___x_672_ = lean_box(0);
    return v___x_672_;
}
pub unsafe fn l_Lake_instInhabitedOrderedTagAttribute_default___lam__3___boxed(
    mut v_x_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_674_: *mut LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Lake_instInhabitedOrderedTagAttribute_default___lam__3(v_x_673_);
    lean_dec_ref(v_x_673_);
    return v_res_674_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4() -> *mut LeanObject
{
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    v___x_679_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
    return v___x_679_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5() -> *mut LeanObject
{
    let mut v___f_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    v___f_680_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__3;
    v___f_681_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__2;
    v___f_682_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__1;
    v___f_683_ = l_Lake_instInhabitedOrderedTagAttribute_default___closed__0;
    v___x_684_ = lean_box(0);
    v___x_685_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__4_once),
        _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__4,
    );
    v___x_686_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_686_, 0, v___x_685_);
    lean_ctor_set(v___x_686_, 1, v___x_684_);
    lean_ctor_set(v___x_686_, 2, v___f_683_);
    lean_ctor_set(v___x_686_, 3, v___f_682_);
    lean_ctor_set(v___x_686_, 4, v___f_681_);
    lean_ctor_set(v___x_686_, 5, v___f_680_);
    return v___x_686_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6() -> *mut LeanObject
{
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__5_once),
        _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__5,
    );
    v___x_688_ = l_Lean_instInhabitedAttributeImpl_default;
    v___x_689_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_689_, 0, v___x_688_);
    lean_ctor_set(v___x_689_, 1, v___x_687_);
    return v___x_689_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute_default() -> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__6),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedOrderedTagAttribute_default___closed__6_once),
        _init_l_Lake_instInhabitedOrderedTagAttribute_default___closed__6,
    );
    return v___x_690_;
}
pub unsafe fn _init_l_Lake_instInhabitedOrderedTagAttribute() -> *mut LeanObject {
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lake_instInhabitedOrderedTagAttribute_default;
    return v___x_691_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    v___x_718_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__10;
    v___x_719_ = l_Lean_mkAtom(v___x_718_);
    return v___x_719_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    v___x_720_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__12_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__12,
    );
    v___x_721_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_722_ = lean_array_push(v___x_721_, v___x_720_);
    return v___x_722_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__17;
    v___x_732_ = l_Lean_mkAtom(v___x_731_);
    return v___x_732_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    v___x_733_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__18_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__18,
    );
    v___x_734_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_735_ = lean_array_push(v___x_734_, v___x_733_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    v___x_736_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__19_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__19,
    );
    v___x_737_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__16;
    v___x_738_ = lean_box(2);
    v___x_739_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_739_, 0, v___x_738_);
    lean_ctor_set(v___x_739_, 1, v___x_737_);
    lean_ctor_set(v___x_739_, 2, v___x_736_);
    return v___x_739_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_740_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__20_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__20,
    );
    v___x_741_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__13_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__13,
    );
    v___x_742_ = lean_array_push(v___x_741_, v___x_740_);
    return v___x_742_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__21_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__21,
    );
    v___x_744_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__11;
    v___x_745_ = lean_box(2);
    v___x_746_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_746_, 0, v___x_745_);
    lean_ctor_set(v___x_746_, 1, v___x_744_);
    lean_ctor_set(v___x_746_, 2, v___x_743_);
    return v___x_746_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__22_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__22,
    );
    v___x_748_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_749_ = lean_array_push(v___x_748_, v___x_747_);
    return v___x_749_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__23_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__23,
    );
    v___x_751_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__9;
    v___x_752_ = lean_box(2);
    v___x_753_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_753_, 0, v___x_752_);
    lean_ctor_set(v___x_753_, 1, v___x_751_);
    lean_ctor_set(v___x_753_, 2, v___x_750_);
    return v___x_753_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___x_754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__24_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__24,
    );
    v___x_755_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_756_ = lean_array_push(v___x_755_, v___x_754_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__25_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__25,
    );
    v___x_758_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__7;
    v___x_759_ = lean_box(2);
    v___x_760_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_760_, 0, v___x_759_);
    lean_ctor_set(v___x_760_, 1, v___x_758_);
    lean_ctor_set(v___x_760_, 2, v___x_757_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v___x_761_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__26_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__26,
    );
    v___x_762_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__5;
    v___x_763_ = lean_array_push(v___x_762_, v___x_761_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__27_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__27,
    );
    v___x_765_ = l_Lake_registerOrderedTagAttribute___auto__1___closed__4;
    v___x_766_ = lean_box(2);
    v___x_767_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_767_, 0, v___x_766_);
    lean_ctor_set(v___x_767_, 1, v___x_765_);
    lean_ctor_set(v___x_767_, 2, v___x_764_);
    return v___x_767_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___auto__1() -> *mut LeanObject {
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    v___x_768_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___auto__1___closed__28_once),
        _init_l_Lake_registerOrderedTagAttribute___auto__1___closed__28,
    );
    return v___x_768_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__0(
    mut v_es_769_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_es_769_);
    return v_es_769_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__0___boxed(
    mut v_es_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_771_: *mut LeanObject = core::ptr::null_mut();
    v_res_771_ = l_Lake_registerOrderedTagAttribute___lam__0(v_es_770_);
    lean_dec_ref(v_es_770_);
    return v_res_771_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__1(
    mut v_s_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lake_registerOrderedTagAttribute___lam__1___closed__5;
    v___x_786_ = lean_array_get_size(v_s_784_);
    v___x_787_ = l_Nat_reprFast(v___x_786_);
    v___x_788_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_788_, 0, v___x_787_);
    v___x_789_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_789_, 0, v___x_785_);
    lean_ctor_set(v___x_789_, 1, v___x_788_);
    return v___x_789_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__1___boxed(
    mut v_s_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lake_registerOrderedTagAttribute___lam__1(v_s_790_);
    lean_dec_ref(v_s_790_);
    return v_res_791_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__2(
    mut v_x_792_: *mut LeanObject,
    mut v_s_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_s_793_, 2);
    v___x_794_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_794_, 0, v_s_793_);
    lean_ctor_set(v___x_794_, 1, v_s_793_);
    lean_ctor_set(v___x_794_, 2, v_s_793_);
    return v___x_794_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__2___boxed(
    mut v_x_795_: *mut LeanObject,
    mut v_s_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_797_: *mut LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Lake_registerOrderedTagAttribute___lam__2(v_x_795_, v_s_796_);
    lean_dec_ref(v_x_795_);
    return v_res_797_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__3(
    mut v_s_798_: *mut LeanObject,
    mut v_n_799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    v___x_800_ = lean_array_push(v_s_798_, v_n_799_);
    return v___x_800_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__4(
    mut v___x_801_: *mut LeanObject,
    mut v_x_802_: *mut LeanObject,
    mut v_x_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    v___x_805_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_805_, 0, v___x_801_);
    return v___x_805_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__4___boxed(
    mut v___x_806_: *mut LeanObject,
    mut v_x_807_: *mut LeanObject,
    mut v_x_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_810_: *mut LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Lake_registerOrderedTagAttribute___lam__4(v___x_806_, v_x_807_, v_x_808_);
    lean_dec_ref(v_x_808_);
    lean_dec_ref(v_x_807_);
    return v_res_810_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__5(
    mut v___x_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    v___x_813_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_813_, 0, v___x_811_);
    return v___x_813_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__5___boxed(
    mut v___x_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_816_: *mut LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lake_registerOrderedTagAttribute___lam__5(v___x_814_);
    return v_res_816_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    v___x_817_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_817_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    v___x_818_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__0);
    v___x_819_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_819_, 0, v___x_818_);
    return v___x_819_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    v___x_820_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
    v___x_821_ = lean_unsigned_to_nat(0);
    v___x_822_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_822_, 0, v___x_821_);
    lean_ctor_set(v___x_822_, 1, v___x_821_);
    lean_ctor_set(v___x_822_, 2, v___x_821_);
    lean_ctor_set(v___x_822_, 3, v___x_821_);
    lean_ctor_set(v___x_822_, 4, v___x_820_);
    lean_ctor_set(v___x_822_, 5, v___x_820_);
    lean_ctor_set(v___x_822_, 6, v___x_820_);
    lean_ctor_set(v___x_822_, 7, v___x_820_);
    lean_ctor_set(v___x_822_, 8, v___x_820_);
    lean_ctor_set(v___x_822_, 9, v___x_820_);
    return v___x_822_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    v___x_823_ = lean_unsigned_to_nat(32);
    v___x_824_ = lean_mk_empty_array_with_capacity(v___x_823_);
    v___x_825_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_825_, 0, v___x_824_);
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_826_: usize = 0;
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_826_ = 5usize;
    v___x_827_ = lean_unsigned_to_nat(0);
    v___x_828_ = lean_unsigned_to_nat(32);
    v___x_829_ = lean_mk_empty_array_with_capacity(v___x_828_);
    v___x_830_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__3);
    v___x_831_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_831_, 0, v___x_830_);
    lean_ctor_set(v___x_831_, 1, v___x_829_);
    lean_ctor_set(v___x_831_, 2, v___x_827_);
    lean_ctor_set(v___x_831_, 3, v___x_827_);
    lean_ctor_set_usize(v___x_831_, 4, v___x_826_);
    return v___x_831_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = lean_box(1);
    v___x_833_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__4);
    v___x_834_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__1);
    v___x_835_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_835_, 0, v___x_834_);
    lean_ctor_set(v___x_835_, 1, v___x_833_);
    lean_ctor_set(v___x_835_, 2, v___x_832_);
    return v___x_835_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(
    mut v_msgData_836_: *mut LeanObject,
    mut v___y_837_: *mut LeanObject,
    mut v___y_838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = lean_st_ref_get(v___y_838_);
    v_env_841_ = lean_ctor_get(v___x_840_, 0);
    lean_inc_ref(v_env_841_);
    lean_dec(v___x_840_);
    v_options_842_ = lean_ctor_get(v___y_837_, 2);
    v___x_843_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__2);
    v___x_844_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_842_);
    v___x_845_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_845_, 0, v_env_841_);
    lean_ctor_set(v___x_845_, 1, v___x_843_);
    lean_ctor_set(v___x_845_, 2, v___x_844_);
    lean_ctor_set(v___x_845_, 3, v_options_842_);
    v___x_846_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_846_, 0, v___x_845_);
    lean_ctor_set(v___x_846_, 1, v_msgData_836_);
    v___x_847_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_847_, 0, v___x_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0___boxed(
    mut v_msgData_848_: *mut LeanObject,
    mut v___y_849_: *mut LeanObject,
    mut v___y_850_: *mut LeanObject,
    mut v___y_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_852_: *mut LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msgData_848_, v___y_849_, v___y_850_);
    lean_dec(v___y_850_);
    lean_dec_ref(v___y_849_);
    return v_res_852_;
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
    mut v_msg_853_: *mut LeanObject,
    mut v___y_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_857_ = lean_ctor_get(v___y_854_, 5);
                v___x_858_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0_spec__0(v_msg_853_, v___y_854_, v___y_855_);
                v_a_859_ = lean_ctor_get(v___x_858_, 0);
                v_isSharedCheck_867_ = (!lean_is_exclusive(v___x_858_)) as u8;
                if v_isSharedCheck_867_ == 0 {
                    v___x_861_ = v___x_858_;
                    v_isShared_862_ = v_isSharedCheck_867_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_859_);
                    lean_dec(v___x_858_);
                    v___x_861_ = lean_box(0);
                    v_isShared_862_ = v_isSharedCheck_867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_857_);
                v___x_863_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_863_, 0, v_ref_857_);
                lean_ctor_set(v___x_863_, 1, v_a_859_);
                if v_isShared_862_ == 0 {
                    lean_ctor_set_tag(v___x_861_, 1);
                    lean_ctor_set(v___x_861_, 0, v___x_863_);
                    v___x_865_ = v___x_861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
                    v___x_865_ = v_reuseFailAlloc_866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg___boxed(
    mut v_msg_868_: *mut LeanObject,
    mut v___y_869_: *mut LeanObject,
    mut v___y_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_872_: *mut LeanObject = core::ptr::null_mut();
    v_res_872_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v_msg_868_, v___y_869_, v___y_870_,
    );
    lean_dec(v___y_870_);
    lean_dec_ref(v___y_869_);
    return v_res_872_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1() -> *mut LeanObject {
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Lake_registerOrderedTagAttribute___lam__6___closed__0;
    v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
    return v___x_875_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3() -> *mut LeanObject {
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = l_Lake_registerOrderedTagAttribute___lam__6___closed__2;
    v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
    return v___x_878_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__6(
    mut v_name_879_: *mut LeanObject,
    mut v_decl_880_: *mut LeanObject,
    mut v___y_881_: *mut LeanObject,
    mut v___y_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    v___x_884_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__1),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__1_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__1,
    );
    v___x_885_ = l_Lean_MessageData_ofName(v_name_879_);
    v___x_886_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_886_, 0, v___x_884_);
    lean_ctor_set(v___x_886_, 1, v___x_885_);
    v___x_887_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__3),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__6___closed__3_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__6___closed__3,
    );
    v___x_888_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_888_, 0, v___x_886_);
    lean_ctor_set(v___x_888_, 1, v___x_887_);
    v___x_889_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v___x_888_, v___y_881_, v___y_882_,
    );
    return v___x_889_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__6___boxed(
    mut v_name_890_: *mut LeanObject,
    mut v_decl_891_: *mut LeanObject,
    mut v___y_892_: *mut LeanObject,
    mut v___y_893_: *mut LeanObject,
    mut v___y_894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_895_: *mut LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lake_registerOrderedTagAttribute___lam__6(
        v_name_890_,
        v_decl_891_,
        v___y_892_,
        v___y_893_,
    );
    lean_dec(v___y_893_);
    lean_dec_ref(v___y_892_);
    lean_dec(v_decl_891_);
    return v_res_895_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    v___x_897_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__0;
    v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__2;
    v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
    return v___x_901_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__4;
    v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
    return v___x_904_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(
    mut v_name_908_: *mut LeanObject,
    mut v_kind_909_: u8,
    mut v___y_910_: *mut LeanObject,
    mut v___y_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_913_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__1);
                v___x_914_ = l_Lean_MessageData_ofName(v_name_908_);
                v___x_915_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_915_, 0, v___x_913_);
                lean_ctor_set(v___x_915_, 1, v___x_914_);
                v___x_916_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__3);
                v___x_917_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_917_, 0, v___x_915_);
                lean_ctor_set(v___x_917_, 1, v___x_916_);
                match v_kind_909_ {
                    0 => {
                        v___x_926_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__6;
                        v___y_919_ = v___x_926_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_927_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__7;
                        v___y_919_ = v___x_927_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_928_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__8;
                        v___y_919_ = v___x_928_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_919_);
                v___x_920_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_920_, 0, v___y_919_);
                v___x_921_ = l_Lean_MessageData_ofFormat(v___x_920_);
                v___x_922_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_922_, 0, v___x_917_);
                lean_ctor_set(v___x_922_, 1, v___x_921_);
                v___x_923_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___closed__5);
                v___x_924_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_924_, 0, v___x_922_);
                lean_ctor_set(v___x_924_, 1, v___x_923_);
                v___x_925_ =
                    l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
                        v___x_924_, v___y_910_, v___y_911_,
                    );
                return v___x_925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg___boxed(
    mut v_name_929_: *mut LeanObject,
    mut v_kind_930_: *mut LeanObject,
    mut v___y_931_: *mut LeanObject,
    mut v___y_932_: *mut LeanObject,
    mut v___y_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_934_: u8 = 0;
    let mut v_res_935_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_934_ = (lean_unbox(v_kind_930_) as u8);
    v_res_935_ =
        l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(
            v_name_929_,
            v_kind_boxed_934_,
            v___y_931_,
            v___y_932_,
        );
    lean_dec(v___y_932_);
    lean_dec_ref(v___y_931_);
    return v_res_935_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    v___x_937_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__0;
    v___x_938_ = l_Lean_stringToMessageData(v___x_937_);
    return v___x_938_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    v___x_940_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__2;
    v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
    return v___x_941_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__4;
    v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
    return v___x_944_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(
    mut v_attrName_945_: *mut LeanObject,
    mut v_declName_946_: *mut LeanObject,
    mut v___y_947_: *mut LeanObject,
    mut v___y_948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    v___x_950_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__1);
    v___x_951_ = l_Lean_MessageData_ofName(v_attrName_945_);
    v___x_952_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_952_, 0, v___x_950_);
    lean_ctor_set(v___x_952_, 1, v___x_951_);
    v___x_953_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__3);
    v___x_954_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_954_, 0, v___x_952_);
    lean_ctor_set(v___x_954_, 1, v___x_953_);
    v___x_955_ = 0;
    v___x_956_ = l_Lean_MessageData_ofConstName(v_declName_946_, v___x_955_);
    v___x_957_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_957_, 0, v___x_954_);
    lean_ctor_set(v___x_957_, 1, v___x_956_);
    v___x_958_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___closed__5);
    v___x_959_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_959_, 0, v___x_957_);
    lean_ctor_set(v___x_959_, 1, v___x_958_);
    v___x_960_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v___x_959_, v___y_947_, v___y_948_,
    );
    return v___x_960_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg___boxed(
    mut v_attrName_961_: *mut LeanObject,
    mut v_declName_962_: *mut LeanObject,
    mut v___y_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_966_: *mut LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_961_, v_declName_962_, v___y_963_, v___y_964_);
    lean_dec(v___y_964_);
    lean_dec_ref(v___y_963_);
    return v_res_966_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0() -> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_967_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1() -> *mut LeanObject {
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    v___x_968_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__0),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__0_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__0,
    );
    v___x_969_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_969_, 0, v___x_968_);
    return v___x_969_;
}
pub unsafe fn _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2() -> *mut LeanObject {
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    v___x_970_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__1),
        core::ptr::addr_of_mut!(l_Lake_registerOrderedTagAttribute___lam__7___closed__1_once),
        _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__1,
    );
    v___x_971_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_971_, 0, v___x_970_);
    lean_ctor_set(v___x_971_, 1, v___x_970_);
    return v___x_971_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__7(
    mut v_validate_972_: *mut LeanObject,
    mut v_a_973_: *mut LeanObject,
    mut v_name_974_: *mut LeanObject,
    mut v_decl_975_: *mut LeanObject,
    mut v_stx_976_: *mut LeanObject,
    mut v_kind_977_: u8,
    mut v___y_978_: *mut LeanObject,
    mut v___y_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_987_: u8 = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1000_: u8 = 0;
    let mut v_asyncMode_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1013_: u8 = 0;
    let mut v_unused_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1015_: u8 = 0;
    let mut v_unused_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u8 = 0;
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1024_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_976_, v___y_978_, v___y_979_);
                if lean_obj_tag(v___x_1024_) == 0 {
                    lean_dec_ref_known(v___x_1024_, 1);
                    v___x_1025_ = 0;
                    v___x_1026_ = l_Lean_instBEqAttributeKind_beq(v_kind_977_, v___x_1025_);
                    if v___x_1026_ == 0 {
                        lean_dec(v_decl_975_);
                        lean_dec_ref(v_a_973_);
                        lean_dec_ref(v_validate_972_);
                        v___x_1027_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(v_name_974_, v_kind_977_, v___y_978_, v___y_979_);
                        return v___x_1027_;
                    } else {
                        v___y_1018_ = v___y_978_;
                        v___y_1019_ = v___y_979_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_decl_975_);
                    lean_dec(v_name_974_);
                    lean_dec_ref(v_a_973_);
                    lean_dec_ref(v_validate_972_);
                    return v___x_1024_;
                }
            }
            1 => {
                lean_inc(v___y_983_);
                lean_inc_ref(v___y_982_);
                lean_inc(v_decl_975_);
                v___x_984_ = lean_apply_4(
                    v_validate_972_,
                    v_decl_975_,
                    v___y_982_,
                    v___y_983_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_984_) == 0 {
                    v_isSharedCheck_1015_ = (!lean_is_exclusive(v___x_984_)) as u8;
                    if v_isSharedCheck_1015_ == 0 {
                        v_unused_1016_ = lean_ctor_get(v___x_984_, 0);
                        lean_dec(v_unused_1016_);
                        v___x_986_ = v___x_984_;
                        v_isShared_987_ = v_isSharedCheck_1015_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_984_);
                        v___x_986_ = lean_box(0);
                        v_isShared_987_ = v_isSharedCheck_1015_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_decl_975_);
                    lean_dec_ref(v_a_973_);
                    return v___x_984_;
                }
            }
            2 => {
                v___x_988_ = lean_st_ref_take(v___y_983_);
                v_toEnvExtension_989_ = lean_ctor_get(v_a_973_, 0);
                v_env_990_ = lean_ctor_get(v___x_988_, 0);
                v_nextMacroScope_991_ = lean_ctor_get(v___x_988_, 1);
                v_ngen_992_ = lean_ctor_get(v___x_988_, 2);
                v_auxDeclNGen_993_ = lean_ctor_get(v___x_988_, 3);
                v_traceState_994_ = lean_ctor_get(v___x_988_, 4);
                v_messages_995_ = lean_ctor_get(v___x_988_, 6);
                v_infoState_996_ = lean_ctor_get(v___x_988_, 7);
                v_snapshotTasks_997_ = lean_ctor_get(v___x_988_, 8);
                v_isSharedCheck_1013_ = (!lean_is_exclusive(v___x_988_)) as u8;
                if v_isSharedCheck_1013_ == 0 {
                    v_unused_1014_ = lean_ctor_get(v___x_988_, 5);
                    lean_dec(v_unused_1014_);
                    v___x_999_ = v___x_988_;
                    v_isShared_1000_ = v_isSharedCheck_1013_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_997_);
                    lean_inc(v_infoState_996_);
                    lean_inc(v_messages_995_);
                    lean_inc(v_traceState_994_);
                    lean_inc(v_auxDeclNGen_993_);
                    lean_inc(v_ngen_992_);
                    lean_inc(v_nextMacroScope_991_);
                    lean_inc(v_env_990_);
                    lean_dec(v___x_988_);
                    v___x_999_ = lean_box(0);
                    v_isShared_1000_ = v_isSharedCheck_1013_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_asyncMode_1001_ = lean_ctor_get(v_toEnvExtension_989_, 2);
                lean_inc(v_asyncMode_1001_);
                v___x_1002_ = lean_box(0);
                v___x_1003_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_a_973_,
                    v_env_990_,
                    v_decl_975_,
                    v_asyncMode_1001_,
                    v___x_1002_,
                );
                lean_dec(v_asyncMode_1001_);
                v___x_1004_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lake_registerOrderedTagAttribute___lam__7___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lake_registerOrderedTagAttribute___lam__7___closed__2_once
                    ),
                    _init_l_Lake_registerOrderedTagAttribute___lam__7___closed__2,
                );
                if v_isShared_1000_ == 0 {
                    lean_ctor_set(v___x_999_, 5, v___x_1004_);
                    lean_ctor_set(v___x_999_, 0, v___x_1003_);
                    v___x_1006_ = v___x_999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1003_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_nextMacroScope_991_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_ngen_992_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_auxDeclNGen_993_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_traceState_994_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 5, v___x_1004_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 6, v_messages_995_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 7, v_infoState_996_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_snapshotTasks_997_);
                    v___x_1006_ = v_reuseFailAlloc_1012_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1007_ = lean_st_ref_set(v___y_983_, v___x_1006_);
                v___x_1008_ = lean_box(0);
                if v_isShared_987_ == 0 {
                    lean_ctor_set(v___x_986_, 0, v___x_1008_);
                    v___x_1010_ = v___x_986_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
                    v___x_1010_ = v_reuseFailAlloc_1011_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1010_;
            }
            6 => {
                v___x_1020_ = lean_st_ref_get(v___y_1019_);
                v_env_1021_ = lean_ctor_get(v___x_1020_, 0);
                lean_inc_ref(v_env_1021_);
                lean_dec(v___x_1020_);
                v___x_1022_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1021_, v_decl_975_);
                lean_dec_ref(v_env_1021_);
                if lean_obj_tag(v___x_1022_) == 0 {
                    lean_dec(v_name_974_);
                    v___y_982_ = v___y_1018_;
                    v___y_983_ = v___y_1019_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_1022_, 1);
                    lean_dec_ref(v_a_973_);
                    lean_dec_ref(v_validate_972_);
                    v___x_1023_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_name_974_, v_decl_975_, v___y_1018_, v___y_1019_);
                    return v___x_1023_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___lam__7___boxed(
    mut v_validate_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
    mut v_name_1030_: *mut LeanObject,
    mut v_decl_1031_: *mut LeanObject,
    mut v_stx_1032_: *mut LeanObject,
    mut v_kind_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
    mut v___y_1035_: *mut LeanObject,
    mut v___y_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_1037_: u8 = 0;
    let mut v_res_1038_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_1037_ = (lean_unbox(v_kind_1033_) as u8);
    v_res_1038_ = l_Lake_registerOrderedTagAttribute___lam__7(
        v_validate_1028_,
        v_a_1029_,
        v_name_1030_,
        v_decl_1031_,
        v_stx_1032_,
        v_kind_boxed_1037_,
        v___y_1034_,
        v___y_1035_,
    );
    lean_dec(v___y_1035_);
    lean_dec_ref(v___y_1034_);
    return v_res_1038_;
}
pub unsafe fn l_Lake_registerOrderedTagAttribute(
    mut v_name_1049_: *mut LeanObject,
    mut v_descr_1050_: *mut LeanObject,
    mut v_validate_1051_: *mut LeanObject,
    mut v_ref_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut v_unused_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1088_: u8 = 0;
    let mut v_a_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1092_: u8 = 0;
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1054_ = l_Lake_registerOrderedTagAttribute___closed__0;
                v___f_1055_ = l_Lake_registerOrderedTagAttribute___closed__1;
                v___f_1056_ = l_Lake_registerOrderedTagAttribute___closed__2;
                v___f_1057_ = l_Lake_registerOrderedTagAttribute___closed__3;
                v___f_1058_ = l_Lake_registerOrderedTagAttribute___closed__5;
                v___f_1059_ = l_Lake_registerOrderedTagAttribute___closed__6;
                v___x_1060_ = lean_box(2);
                v___x_1061_ = lean_box(0);
                lean_inc(v_ref_1052_);
                v___x_1062_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_1062_, 0, v_ref_1052_);
                lean_ctor_set(v___x_1062_, 1, v___f_1059_);
                lean_ctor_set(v___x_1062_, 2, v___f_1058_);
                lean_ctor_set(v___x_1062_, 3, v___f_1057_);
                lean_ctor_set(v___x_1062_, 4, v___f_1056_);
                lean_ctor_set(v___x_1062_, 5, v___f_1055_);
                lean_ctor_set(v___x_1062_, 6, v___x_1060_);
                lean_ctor_set(v___x_1062_, 7, v___x_1061_);
                v___x_1063_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1063_, 0, v___x_1062_);
                lean_ctor_set(v___x_1063_, 1, v___f_1054_);
                v___x_1064_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1063_);
                if lean_obj_tag(v___x_1064_) == 0 {
                    v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
                    lean_inc_n(v_a_1065_, 2);
                    lean_dec_ref_known(v___x_1064_, 1);
                    lean_inc_n(v_name_1049_, 2);
                    v___f_1066_ = lean_alloc_closure(
                        l_Lake_registerOrderedTagAttribute___lam__6___boxed
                            as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    lean_closure_set(v___f_1066_, 0, v_name_1049_);
                    v___f_1067_ = lean_alloc_closure(
                        l_Lake_registerOrderedTagAttribute___lam__7___boxed
                            as *mut core::ffi::c_void,
                        9,
                        3,
                    );
                    lean_closure_set(v___f_1067_, 0, v_validate_1051_);
                    lean_closure_set(v___f_1067_, 1, v_a_1065_);
                    lean_closure_set(v___f_1067_, 2, v_name_1049_);
                    v___x_1068_ = 0;
                    v___x_1069_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v___x_1069_, 0, v_ref_1052_);
                    lean_ctor_set(v___x_1069_, 1, v_name_1049_);
                    lean_ctor_set(v___x_1069_, 2, v_descr_1050_);
                    lean_ctor_set_uint8(
                        v___x_1069_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_1068_,
                    );
                    v___x_1070_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1070_, 0, v___x_1069_);
                    lean_ctor_set(v___x_1070_, 1, v___f_1067_);
                    lean_ctor_set(v___x_1070_, 2, v___f_1066_);
                    lean_inc_ref(v___x_1070_);
                    v___x_1071_ = l_Lean_registerBuiltinAttribute(v___x_1070_);
                    if lean_obj_tag(v___x_1071_) == 0 {
                        v_isSharedCheck_1079_ = (!lean_is_exclusive(v___x_1071_)) as u8;
                        if v_isSharedCheck_1079_ == 0 {
                            v_unused_1080_ = lean_ctor_get(v___x_1071_, 0);
                            lean_dec(v_unused_1080_);
                            v___x_1073_ = v___x_1071_;
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1071_);
                            v___x_1073_ = lean_box(0);
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_1070_, 3);
                        lean_dec(v_a_1065_);
                        v_a_1081_ = lean_ctor_get(v___x_1071_, 0);
                        v_isSharedCheck_1088_ = (!lean_is_exclusive(v___x_1071_)) as u8;
                        if v_isSharedCheck_1088_ == 0 {
                            v___x_1083_ = v___x_1071_;
                            v_isShared_1084_ = v_isSharedCheck_1088_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1081_);
                            lean_dec(v___x_1071_);
                            v___x_1083_ = lean_box(0);
                            v_isShared_1084_ = v_isSharedCheck_1088_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_ref_1052_);
                    lean_dec_ref(v_validate_1051_);
                    lean_dec_ref(v_descr_1050_);
                    lean_dec(v_name_1049_);
                    v_a_1089_ = lean_ctor_get(v___x_1064_, 0);
                    v_isSharedCheck_1096_ = (!lean_is_exclusive(v___x_1064_)) as u8;
                    if v_isSharedCheck_1096_ == 0 {
                        v___x_1091_ = v___x_1064_;
                        v_isShared_1092_ = v_isSharedCheck_1096_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1089_);
                        lean_dec(v___x_1064_);
                        v___x_1091_ = lean_box(0);
                        v_isShared_1092_ = v_isSharedCheck_1096_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1075_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1075_, 0, v___x_1070_);
                lean_ctor_set(v___x_1075_, 1, v_a_1065_);
                if v_isShared_1074_ == 0 {
                    lean_ctor_set(v___x_1073_, 0, v___x_1075_);
                    v___x_1077_ = v___x_1073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
                    v___x_1077_ = v_reuseFailAlloc_1078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1077_;
            }
            3 => {
                if v_isShared_1084_ == 0 {
                    v___x_1086_ = v___x_1083_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
                    v___x_1086_ = v_reuseFailAlloc_1087_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1086_;
            }
            5 => {
                if v_isShared_1092_ == 0 {
                    v___x_1094_ = v___x_1091_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
                    v___x_1094_ = v_reuseFailAlloc_1095_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_registerOrderedTagAttribute___boxed(
    mut v_name_1097_: *mut LeanObject,
    mut v_descr_1098_: *mut LeanObject,
    mut v_validate_1099_: *mut LeanObject,
    mut v_ref_1100_: *mut LeanObject,
    mut v_a_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1102_: *mut LeanObject = core::ptr::null_mut();
    v_res_1102_ = l_Lake_registerOrderedTagAttribute(
        v_name_1097_,
        v_descr_1098_,
        v_validate_1099_,
        v_ref_1100_,
    );
    return v_res_1102_;
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(
    mut v_00_u03b1_1103_: *mut LeanObject,
    mut v_msg_1104_: *mut LeanObject,
    mut v___y_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    v___x_1108_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___redArg(
        v_msg_1104_,
        v___y_1105_,
        v___y_1106_,
    );
    return v___x_1108_;
}
pub unsafe fn l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0___boxed(
    mut v_00_u03b1_1109_: *mut LeanObject,
    mut v_msg_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1114_: *mut LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_Lean_throwError___at___00Lake_registerOrderedTagAttribute_spec__0(
        v_00_u03b1_1109_,
        v_msg_1110_,
        v___y_1111_,
        v___y_1112_,
    );
    lean_dec(v___y_1112_);
    lean_dec_ref(v___y_1111_);
    return v_res_1114_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(
    mut v_00_u03b1_1115_: *mut LeanObject,
    mut v_attrName_1116_: *mut LeanObject,
    mut v_declName_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
    mut v___y_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___redArg(v_attrName_1116_, v_declName_1117_, v___y_1118_, v___y_1119_);
    return v___x_1121_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1___boxed(
    mut v_00_u03b1_1122_: *mut LeanObject,
    mut v_attrName_1123_: *mut LeanObject,
    mut v_declName_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1128_: *mut LeanObject = core::ptr::null_mut();
    v_res_1128_ =
        l_Lean_throwAttrDeclInImportedModule___at___00Lake_registerOrderedTagAttribute_spec__1(
            v_00_u03b1_1122_,
            v_attrName_1123_,
            v_declName_1124_,
            v___y_1125_,
            v___y_1126_,
        );
    lean_dec(v___y_1126_);
    lean_dec_ref(v___y_1125_);
    return v_res_1128_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(
    mut v_00_u03b1_1129_: *mut LeanObject,
    mut v_name_1130_: *mut LeanObject,
    mut v_kind_1131_: u8,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ =
        l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___redArg(
            v_name_1130_,
            v_kind_1131_,
            v___y_1132_,
            v___y_1133_,
        );
    return v___x_1135_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2___boxed(
    mut v_00_u03b1_1136_: *mut LeanObject,
    mut v_name_1137_: *mut LeanObject,
    mut v_kind_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_1142_: u8 = 0;
    let mut v_res_1143_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_1142_ = (lean_unbox(v_kind_1138_) as u8);
    v_res_1143_ = l_Lean_throwAttrMustBeGlobal___at___00Lake_registerOrderedTagAttribute_spec__2(
        v_00_u03b1_1136_,
        v_name_1137_,
        v_kind_boxed_1142_,
        v___y_1139_,
        v___y_1140_,
    );
    lean_dec(v___y_1140_);
    lean_dec_ref(v___y_1139_);
    return v_res_1143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(
    mut v_a_1144_: *mut LeanObject,
    mut v_as_1145_: *mut LeanObject,
    mut v_i_1146_: usize,
    mut v_stop_1147_: usize,
) -> u8 {
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: usize = 0;
    let mut v___x_1152_: usize = 0;
    let mut v___x_1154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1148_ = lean_usize_dec_eq(v_i_1146_, v_stop_1147_);
                if v___x_1148_ == 0 {
                    v___x_1149_ = lean_array_uget_borrowed(v_as_1145_, v_i_1146_);
                    v___x_1150_ = lean_name_eq(v_a_1144_, v___x_1149_);
                    if v___x_1150_ == 0 {
                        v___x_1151_ = 1usize;
                        v___x_1152_ = lean_usize_add(v_i_1146_, v___x_1151_);
                        v_i_1146_ = v___x_1152_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1150_;
                    }
                } else {
                    v___x_1154_ = 0;
                    return v___x_1154_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0___boxed(
    mut v_a_1155_: *mut LeanObject,
    mut v_as_1156_: *mut LeanObject,
    mut v_i_1157_: *mut LeanObject,
    mut v_stop_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1159_: usize = 0;
    let mut v_stop_boxed_1160_: usize = 0;
    let mut v_res_1161_: u8 = 0;
    let mut v_r_1162_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1159_ = lean_unbox_usize(v_i_1157_);
    lean_dec(v_i_1157_);
    v_stop_boxed_1160_ = lean_unbox_usize(v_stop_1158_);
    lean_dec(v_stop_1158_);
    v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_1155_, v_as_1156_, v_i_boxed_1159_, v_stop_boxed_1160_);
    lean_dec_ref(v_as_1156_);
    lean_dec(v_a_1155_);
    v_r_1162_ = lean_box((v_res_1161_) as usize);
    return v_r_1162_;
}
pub unsafe fn l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(
    mut v_as_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
) -> u8 {
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    v___x_1165_ = lean_unsigned_to_nat(0);
    v___x_1166_ = lean_array_get_size(v_as_1163_);
    v___x_1167_ = lean_nat_dec_lt(v___x_1165_, v___x_1166_);
    if v___x_1167_ == 0 {
        return v___x_1167_;
    } else {
        if v___x_1167_ == 0 {
            return v___x_1167_;
        } else {
            let mut v___x_1168_: usize = 0;
            let mut v___x_1169_: usize = 0;
            let mut v___x_1170_: u8 = 0;
            v___x_1168_ = 0usize;
            v___x_1169_ = lean_usize_of_nat(v___x_1166_);
            v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0_spec__0(v_a_1164_, v_as_1163_, v___x_1168_, v___x_1169_);
            return v___x_1170_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0___boxed(
    mut v_as_1171_: *mut LeanObject,
    mut v_a_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1173_: u8 = 0;
    let mut v_r_1174_: *mut LeanObject = core::ptr::null_mut();
    v_res_1173_ =
        l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(v_as_1171_, v_a_1172_);
    lean_dec(v_a_1172_);
    lean_dec_ref(v_as_1171_);
    v_r_1174_ = lean_box((v_res_1173_) as usize);
    return v_r_1174_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
    mut v_as_1175_: *mut LeanObject,
    mut v_k_1176_: *mut LeanObject,
    mut v_x_1177_: *mut LeanObject,
    mut v_x_1178_: *mut LeanObject,
) -> u8 {
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: u8 = 0;
    let mut v___x_1184_: u8 = 0;
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: u8 = 0;
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1179_ = lean_nat_add(v_x_1177_, v_x_1178_);
                v___x_1180_ = lean_unsigned_to_nat(1);
                v_m_1181_ = lean_nat_shiftr(v___x_1179_, v___x_1180_);
                lean_dec(v___x_1179_);
                v_a_1182_ = lean_array_fget_borrowed(v_as_1175_, v_m_1181_);
                v___x_1183_ = l_Lean_Name_quickLt(v_a_1182_, v_k_1176_);
                if v___x_1183_ == 0 {
                    lean_dec(v_x_1178_);
                    v___x_1184_ = l_Lean_Name_quickLt(v_k_1176_, v_a_1182_);
                    if v___x_1184_ == 0 {
                        lean_dec(v_m_1181_);
                        lean_dec(v_x_1177_);
                        v___x_1185_ = 1;
                        return v___x_1185_;
                    } else {
                        v___x_1186_ = lean_unsigned_to_nat(0);
                        v___x_1187_ = lean_nat_dec_eq(v_m_1181_, v___x_1186_);
                        if v___x_1187_ == 0 {
                            v___x_1188_ = lean_nat_sub(v_m_1181_, v___x_1180_);
                            lean_dec(v_m_1181_);
                            v___x_1189_ = lean_nat_dec_lt(v___x_1188_, v_x_1177_);
                            if v___x_1189_ == 0 {
                                v_x_1178_ = v___x_1188_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v___x_1188_);
                                lean_dec(v_x_1177_);
                                return v___x_1183_;
                            }
                        } else {
                            lean_dec(v_m_1181_);
                            lean_dec(v_x_1177_);
                            return v___x_1183_;
                        }
                    }
                } else {
                    lean_dec(v_x_1177_);
                    v___x_1191_ = lean_nat_add(v_m_1181_, v___x_1180_);
                    lean_dec(v_m_1181_);
                    v___x_1192_ = lean_nat_dec_le(v___x_1191_, v_x_1178_);
                    if v___x_1192_ == 0 {
                        lean_dec(v___x_1191_);
                        lean_dec(v_x_1178_);
                        return v___x_1192_;
                    } else {
                        v_x_1177_ = v___x_1191_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg___boxed(
    mut v_as_1194_: *mut LeanObject,
    mut v_k_1195_: *mut LeanObject,
    mut v_x_1196_: *mut LeanObject,
    mut v_x_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1198_: u8 = 0;
    let mut v_r_1199_: *mut LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
        v_as_1194_, v_k_1195_, v_x_1196_, v_x_1197_,
    );
    lean_dec(v_k_1195_);
    lean_dec_ref(v_as_1194_);
    v_r_1199_ = lean_box((v_res_1198_) as usize);
    return v_r_1199_;
}
pub unsafe fn _init_l_Lake_OrderedTagAttribute_hasTag___closed__0() -> *mut LeanObject {
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    v___x_1200_ = l_Array_instInhabited(lean_box(0));
    return v___x_1200_;
}
pub unsafe fn l_Lake_OrderedTagAttribute_hasTag(
    mut v_attr_1201_: *mut LeanObject,
    mut v_env_1202_: *mut LeanObject,
    mut v_decl_1203_: *mut LeanObject,
) -> u8 {
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    v___x_1204_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0_once),
        _init_l_Lake_OrderedTagAttribute_hasTag___closed__0,
    );
    v___x_1205_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1202_, v_decl_1203_);
    if lean_obj_tag(v___x_1205_) == 0 {
        let mut v_ext_1206_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toEnvExtension_1207_: *mut LeanObject = core::ptr::null_mut();
        let mut v_asyncMode_1208_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: u8 = 0;
        v_ext_1206_ = lean_ctor_get(v_attr_1201_, 1);
        v_toEnvExtension_1207_ = lean_ctor_get(v_ext_1206_, 0);
        v_asyncMode_1208_ = lean_ctor_get(v_toEnvExtension_1207_, 2);
        v___x_1209_ = lean_box(0);
        v___x_1210_ = l_Lean_PersistentEnvExtension_getState___redArg(
            v___x_1204_,
            v_ext_1206_,
            v_env_1202_,
            v_asyncMode_1208_,
            v___x_1209_,
        );
        v___x_1211_ = l_Array_contains___at___00Lake_OrderedTagAttribute_hasTag_spec__0(
            v___x_1210_,
            v_decl_1203_,
        );
        lean_dec(v___x_1210_);
        return v___x_1211_;
    } else {
        let mut v_val_1212_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ext_1213_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1214_: u8 = 0;
        let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: u8 = 0;
        v_val_1212_ = lean_ctor_get(v___x_1205_, 0);
        lean_inc(v_val_1212_);
        lean_dec_ref_known(v___x_1205_, 1);
        v_ext_1213_ = lean_ctor_get(v_attr_1201_, 1);
        v___x_1214_ = 0;
        v___x_1215_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
            v___x_1204_,
            v_ext_1213_,
            v_env_1202_,
            v_val_1212_,
            v___x_1214_,
        );
        lean_dec(v_val_1212_);
        lean_dec_ref(v_env_1202_);
        v___x_1216_ = lean_unsigned_to_nat(0);
        v___x_1217_ = lean_array_get_size(v___x_1215_);
        v___x_1218_ = lean_nat_dec_lt(v___x_1216_, v___x_1217_);
        if v___x_1218_ == 0 {
            lean_dec_ref(v___x_1215_);
            return v___x_1218_;
        } else {
            let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1221_: u8 = 0;
            v___x_1219_ = lean_unsigned_to_nat(1);
            v___x_1220_ = lean_nat_sub(v___x_1217_, v___x_1219_);
            v___x_1221_ = lean_nat_dec_le(v___x_1216_, v___x_1220_);
            if v___x_1221_ == 0 {
                lean_dec(v___x_1220_);
                lean_dec_ref(v___x_1215_);
                return v___x_1221_;
            } else {
                let mut v___x_1222_: u8 = 0;
                v___x_1222_ =
                    l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
                        v___x_1215_,
                        v_decl_1203_,
                        v___x_1216_,
                        v___x_1220_,
                    );
                lean_dec_ref(v___x_1215_);
                return v___x_1222_;
            }
        }
    }
}
pub unsafe fn l_Lake_OrderedTagAttribute_hasTag___boxed(
    mut v_attr_1223_: *mut LeanObject,
    mut v_env_1224_: *mut LeanObject,
    mut v_decl_1225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1226_: u8 = 0;
    let mut v_r_1227_: *mut LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_Lake_OrderedTagAttribute_hasTag(v_attr_1223_, v_env_1224_, v_decl_1225_);
    lean_dec(v_decl_1225_);
    lean_dec_ref(v_attr_1223_);
    v_r_1227_ = lean_box((v_res_1226_) as usize);
    return v_r_1227_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(
    mut v_as_1228_: *mut LeanObject,
    mut v_k_1229_: *mut LeanObject,
    mut v_x_1230_: *mut LeanObject,
    mut v_x_1231_: *mut LeanObject,
    mut v_x_1232_: *mut LeanObject,
) -> u8 {
    let mut v___x_1233_: u8 = 0;
    v___x_1233_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___redArg(
        v_as_1228_, v_k_1229_, v_x_1230_, v_x_1231_,
    );
    return v___x_1233_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1___boxed(
    mut v_as_1234_: *mut LeanObject,
    mut v_k_1235_: *mut LeanObject,
    mut v_x_1236_: *mut LeanObject,
    mut v_x_1237_: *mut LeanObject,
    mut v_x_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1239_: u8 = 0;
    let mut v_r_1240_: *mut LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Array_binSearchAux___at___00Lake_OrderedTagAttribute_hasTag_spec__1(
        v_as_1234_, v_k_1235_, v_x_1236_, v_x_1237_, v_x_1238_,
    );
    lean_dec(v_k_1235_);
    lean_dec_ref(v_as_1234_);
    v_r_1240_ = lean_box((v_res_1239_) as usize);
    return v_r_1240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(
    mut v_as_1241_: *mut LeanObject,
    mut v_i_1242_: usize,
    mut v_stop_1243_: usize,
    mut v_b_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: usize = 0;
    let mut v___x_1249_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1245_ = lean_usize_dec_eq(v_i_1242_, v_stop_1243_);
                if v___x_1245_ == 0 {
                    v___x_1246_ = lean_array_uget_borrowed(v_as_1241_, v_i_1242_);
                    v___x_1247_ = l_Array_append___redArg(v_b_1244_, v___x_1246_);
                    v___x_1248_ = 1usize;
                    v___x_1249_ = lean_usize_add(v_i_1242_, v___x_1248_);
                    v_i_1242_ = v___x_1249_;
                    v_b_1244_ = v___x_1247_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1244_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0___boxed(
    mut v_as_1251_: *mut LeanObject,
    mut v_i_1252_: *mut LeanObject,
    mut v_stop_1253_: *mut LeanObject,
    mut v_b_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1255_: usize = 0;
    let mut v_stop_boxed_1256_: usize = 0;
    let mut v_res_1257_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1255_ = lean_unbox_usize(v_i_1252_);
    lean_dec(v_i_1252_);
    v_stop_boxed_1256_ = lean_unbox_usize(v_stop_1253_);
    lean_dec(v_stop_1253_);
    v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_as_1251_, v_i_boxed_1255_, v_stop_boxed_1256_, v_b_1254_);
    lean_dec_ref(v_as_1251_);
    return v_res_1257_;
}
pub unsafe fn _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0() -> *mut LeanObject {
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    v___x_1258_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_hasTag___closed__0_once),
        _init_l_Lake_OrderedTagAttribute_hasTag___closed__0,
    );
    v___x_1259_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1258_);
    return v___x_1259_;
}
pub unsafe fn l_Lake_OrderedTagAttribute_getAllEntries(
    mut v_attr_1260_: *mut LeanObject,
    mut v_env_1261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: u8 = 0;
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: usize = 0;
    let mut v___x_1279_: usize = 0;
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: usize = 0;
    let mut v___x_1282_: usize = 0;
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ext_1262_ = lean_ctor_get(v_attr_1260_, 1);
                v_toEnvExtension_1263_ = lean_ctor_get(v_ext_1262_, 0);
                v_asyncMode_1264_ = lean_ctor_get(v_toEnvExtension_1263_, 2);
                v___x_1265_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_OrderedTagAttribute_getAllEntries___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lake_OrderedTagAttribute_getAllEntries___closed__0_once
                    ),
                    _init_l_Lake_OrderedTagAttribute_getAllEntries___closed__0,
                );
                v___x_1266_ = lean_box(0);
                v_s_1267_ =
                    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                        v___x_1265_,
                        v_toEnvExtension_1263_,
                        v_env_1261_,
                        v_asyncMode_1264_,
                        v___x_1266_,
                    );
                v_importedEntries_1272_ = lean_ctor_get(v_s_1267_, 0);
                lean_inc_ref(v_importedEntries_1272_);
                v___x_1273_ = lean_unsigned_to_nat(0);
                v___x_1274_ = l_Lake_registerOrderedTagAttribute___closed__4;
                v___x_1275_ = lean_array_get_size(v_importedEntries_1272_);
                v___x_1276_ = lean_nat_dec_lt(v___x_1273_, v___x_1275_);
                if v___x_1276_ == 0 {
                    lean_dec_ref(v_importedEntries_1272_);
                    v___y_1269_ = v___x_1274_;
                    state = 1;
                    continue;
                } else {
                    v___x_1277_ = lean_nat_dec_le(v___x_1275_, v___x_1275_);
                    if v___x_1277_ == 0 {
                        if v___x_1276_ == 0 {
                            lean_dec_ref(v_importedEntries_1272_);
                            v___y_1269_ = v___x_1274_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1278_ = 0usize;
                            v___x_1279_ = lean_usize_of_nat(v___x_1275_);
                            v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_1272_, v___x_1278_, v___x_1279_, v___x_1274_);
                            lean_dec_ref(v_importedEntries_1272_);
                            v___y_1269_ = v___x_1280_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1281_ = 0usize;
                        v___x_1282_ = lean_usize_of_nat(v___x_1275_);
                        v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrderedTagAttribute_getAllEntries_spec__0(v_importedEntries_1272_, v___x_1281_, v___x_1282_, v___x_1274_);
                        lean_dec_ref(v_importedEntries_1272_);
                        v___y_1269_ = v___x_1283_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_state_1270_ = lean_ctor_get(v_s_1267_, 1);
                lean_inc(v_state_1270_);
                lean_dec(v_s_1267_);
                v___x_1271_ = l_Array_append___redArg(v___y_1269_, v_state_1270_);
                lean_dec(v_state_1270_);
                return v___x_1271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_OrderedTagAttribute_getAllEntries___boxed(
    mut v_attr_1284_: *mut LeanObject,
    mut v_env_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1286_: *mut LeanObject = core::ptr::null_mut();
    v_res_1286_ = l_Lake_OrderedTagAttribute_getAllEntries(v_attr_1284_, v_env_1285_);
    lean_dec_ref(v_attr_1284_);
    return v_res_1286_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_OrderedTagAttribute(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedOrderedTagAttribute_default =
        _init_l_Lake_instInhabitedOrderedTagAttribute_default();
    lean_mark_persistent(l_Lake_instInhabitedOrderedTagAttribute_default);
    l_Lake_instInhabitedOrderedTagAttribute = _init_l_Lake_instInhabitedOrderedTagAttribute();
    lean_mark_persistent(l_Lake_instInhabitedOrderedTagAttribute);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_OrderedTagAttribute(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_registerOrderedTagAttribute___auto__1 =
        _init_l_Lake_registerOrderedTagAttribute___auto__1();
    lean_mark_persistent(l_Lake_registerOrderedTagAttribute___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_OrderedTagAttribute(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OrderedTagAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_OrderedTagAttribute(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_OrderedTagAttribute(builtin);
}
