// Lean compiler output
// Module: Lean.ScopedEnvExtension
// Imports: Lean.Attributes
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_reverse___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom, l_List_lengthTR___redArg, l_id___boxed,
    l_panic___redArg,
};
use crate::r#gen::Init::System::IO::l_instInhabitedEIO___aux__1___boxed;
use crate::r#gen::Init::System::IOError::l_instInhabitedError;
use crate::r#gen::Init::System::ST::l_ST_Prim_Ref_get___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_PersistentEnvExtension_modifyState___redArg, l_Lean_instInhabitedEnvExtension_default,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_set, lean_st_ref_take};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value: LeanStringObject<
    10,
> = LeanStringObject {
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value)
        as *mut LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value: LeanStringObject<
    19,
> = LeanStringObject {
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value)
        as *mut LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value: LeanStringObject<
    6,
> = LeanStringObject {
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value)
        as *mut LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_1: LeanCtorObject<
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_2: LeanCtorObject<
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__2_value)
            as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value: LeanStringObject<
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value: LeanStringObject<
    9,
> = LeanStringObject {
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value)
        as *mut LeanObject;
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_0: LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_1: LeanCtorObject<
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_2: LeanCtorObject<
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
            l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__14_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value: LeanCtorObject<3> =
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
                l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17_value: LeanStringObject<
    11,
> = LeanStringObject {
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
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_ScopedEnvExtension_Descr_name___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value:
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
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1_value:
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
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4_value)
        as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__1_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0_value
) as *mut LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value:
    LeanStringObject<26> = LeanStringObject {
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
        110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 108, 111, 99, 97, 108, 32, 101, 110, 116,
        114, 105, 101, 115, 58, 32, 0,
    ],
};
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_popScope___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_ScopedEnvExtension_popScope___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ScopedEnvExtension_popScope___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_popScope___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_getState___redArg___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 101, 97, 110, 46, 83, 99, 111, 112, 101, 100, 69, 110, 118, 69, 120, 116, 101, 110,
            115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_getState___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_getState___redArg___closed__1_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            76, 101, 97, 110, 46, 83, 99, 111, 112, 101, 100, 69, 110, 118, 69, 120, 116, 101, 110,
            115, 105, 111, 110, 46, 103, 101, 116, 83, 116, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_getState___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ScopedEnvExtension_getState___redArg___closed__2_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ScopedEnvExtension_getState___redArg___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ScopedEnvExtension_getState___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_pushScope___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_pushScope___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(
    mut v_x_2602_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2602_) == 0 {
        let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
        v___x_2603_ = lean_unsigned_to_nat(0);
        return v___x_2603_;
    } else {
        let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
        v___x_2604_ = lean_unsigned_to_nat(1);
        return v___x_2604_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg___boxed(
    mut v_x_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2606_: *mut LeanObject = core::ptr::null_mut();
    v_res_2606_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(v_x_2605_);
    lean_dec_ref(v_x_2605_);
    return v_res_2606_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx(
    mut v_00_u03b1_2607_: *mut LeanObject,
    mut v_x_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    v___x_2609_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx___redArg(v_x_2608_);
    return v___x_2609_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorIdx___boxed(
    mut v_00_u03b1_2610_: *mut LeanObject,
    mut v_x_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2612_: *mut LeanObject = core::ptr::null_mut();
    v_res_2612_ = l_Lean_ScopedEnvExtension_Entry_ctorIdx(v_00_u03b1_2610_, v_x_2611_);
    lean_dec_ref(v_x_2611_);
    return v_res_2612_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(
    mut v_t_2613_: *mut LeanObject,
    mut v_k_2614_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_2613_) == 0 {
        let mut v_a_2615_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
        v_a_2615_ = lean_ctor_get(v_t_2613_, 0);
        lean_inc(v_a_2615_);
        lean_dec_ref_known(v_t_2613_, 1);
        v___x_2616_ = lean_apply_1(v_k_2614_, v_a_2615_);
        return v___x_2616_;
    } else {
        let mut v_a_2617_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2618_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
        v_a_2617_ = lean_ctor_get(v_t_2613_, 0);
        lean_inc(v_a_2617_);
        v_a_2618_ = lean_ctor_get(v_t_2613_, 1);
        lean_inc(v_a_2618_);
        lean_dec_ref_known(v_t_2613_, 2);
        v___x_2619_ = lean_apply_2(v_k_2614_, v_a_2617_, v_a_2618_);
        return v___x_2619_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorElim(
    mut v_00_u03b1_2620_: *mut LeanObject,
    mut v_motive_2621_: *mut LeanObject,
    mut v_ctorIdx_2622_: *mut LeanObject,
    mut v_t_2623_: *mut LeanObject,
    mut v_h_2624_: *mut LeanObject,
    mut v_k_2625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    v___x_2626_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2623_, v_k_2625_);
    return v___x_2626_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_ctorElim___boxed(
    mut v_00_u03b1_2627_: *mut LeanObject,
    mut v_motive_2628_: *mut LeanObject,
    mut v_ctorIdx_2629_: *mut LeanObject,
    mut v_t_2630_: *mut LeanObject,
    mut v_h_2631_: *mut LeanObject,
    mut v_k_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2633_: *mut LeanObject = core::ptr::null_mut();
    v_res_2633_ = l_Lean_ScopedEnvExtension_Entry_ctorElim(
        v_00_u03b1_2627_,
        v_motive_2628_,
        v_ctorIdx_2629_,
        v_t_2630_,
        v_h_2631_,
        v_k_2632_,
    );
    lean_dec(v_ctorIdx_2629_);
    return v_res_2633_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_global_elim___redArg(
    mut v_t_2634_: *mut LeanObject,
    mut v_global_2635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2634_, v_global_2635_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_global_elim(
    mut v_00_u03b1_2637_: *mut LeanObject,
    mut v_motive_2638_: *mut LeanObject,
    mut v_t_2639_: *mut LeanObject,
    mut v_h_2640_: *mut LeanObject,
    mut v_global_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    v___x_2642_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2639_, v_global_2641_);
    return v___x_2642_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_scoped_elim___redArg(
    mut v_t_2643_: *mut LeanObject,
    mut v_scoped_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2643_, v_scoped_2644_);
    return v___x_2645_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_Entry_scoped_elim(
    mut v_00_u03b1_2646_: *mut LeanObject,
    mut v_motive_2647_: *mut LeanObject,
    mut v_t_2648_: *mut LeanObject,
    mut v_h_2649_: *mut LeanObject,
    mut v_scoped_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_Lean_ScopedEnvExtension_Entry_ctorElim___redArg(v_t_2648_, v_scoped_2650_);
    return v___x_2651_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    v___x_2652_ = lean_box(0);
    v___x_2653_ = lean_unsigned_to_nat(16);
    v___x_2654_ = lean_mk_array(v___x_2653_, v___x_2652_);
    return v___x_2654_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1()
-> *mut LeanObject {
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    v___x_2655_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__0,
    );
    v___x_2656_ = lean_unsigned_to_nat(0);
    v___x_2657_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2657_, 0, v___x_2656_);
    lean_ctor_set(v___x_2657_, 1, v___x_2655_);
    return v___x_2657_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2()
-> *mut LeanObject {
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2658_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3()
-> *mut LeanObject {
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    v___x_2659_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__2,
    );
    v___x_2660_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2660_, 0, v___x_2659_);
    return v___x_2660_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4()
-> *mut LeanObject {
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    v___x_2661_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__3,
    );
    v___x_2662_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__1,
    );
    v___x_2663_ = 1;
    v___x_2664_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_2664_, 0, v___x_2662_);
    lean_ctor_set(v___x_2664_, 1, v___x_2661_);
    lean_ctor_set_uint8(
        v___x_2664_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_2663_,
    );
    return v___x_2664_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(
    mut v_00_u03b2_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    v___x_2666_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4,
    );
    return v___x_2666_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0()
-> *mut LeanObject {
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default(lean_box(0));
    return v___x_2667_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(
    mut v_a_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    v___x_2669_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__0,
    );
    return v___x_2669_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    v___x_2670_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4,
    );
    v___x_2671_ = lean_box(0);
    v___x_2672_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2672_, 0, v___x_2671_);
    lean_ctor_set(v___x_2672_, 1, v___x_2670_);
    lean_ctor_set(v___x_2672_, 2, v___x_2671_);
    return v___x_2672_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(
    mut v_00_u03b1_2673_: *mut LeanObject,
    mut v_00_u03b2_2674_: *mut LeanObject,
    mut v_00_u03c3_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    v___x_2676_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack_default___closed__0,
    );
    return v___x_2676_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0()
-> *mut LeanObject {
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    v___x_2677_ = l_Lean_ScopedEnvExtension_instInhabitedStateStack_default(
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_2677_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedStateStack(
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    v___x_2681_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once),
        _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0,
    );
    return v___x_2681_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12()
-> *mut LeanObject {
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    v___x_2708_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__10;
    v___x_2709_ = l_Lean_mkAtom(v___x_2708_);
    return v___x_2709_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13()
-> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    v___x_2710_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__12,
    );
    v___x_2711_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2712_ = lean_array_push(v___x_2711_, v___x_2710_);
    return v___x_2712_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18()
-> *mut LeanObject {
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__17;
    v___x_2722_ = l_Lean_mkAtom(v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19()
-> *mut LeanObject {
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___x_2723_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__18,
    );
    v___x_2724_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2725_ = lean_array_push(v___x_2724_, v___x_2723_);
    return v___x_2725_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20()
-> *mut LeanObject {
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    v___x_2726_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__19,
    );
    v___x_2727_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__16;
    v___x_2728_ = lean_box(2);
    v___x_2729_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2729_, 0, v___x_2728_);
    lean_ctor_set(v___x_2729_, 1, v___x_2727_);
    lean_ctor_set(v___x_2729_, 2, v___x_2726_);
    return v___x_2729_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21()
-> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__20,
    );
    v___x_2731_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__13,
    );
    v___x_2732_ = lean_array_push(v___x_2731_, v___x_2730_);
    return v___x_2732_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22()
-> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__21,
    );
    v___x_2734_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__11;
    v___x_2735_ = lean_box(2);
    v___x_2736_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2736_, 0, v___x_2735_);
    lean_ctor_set(v___x_2736_, 1, v___x_2734_);
    lean_ctor_set(v___x_2736_, 2, v___x_2733_);
    return v___x_2736_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23()
-> *mut LeanObject {
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    v___x_2737_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__22,
    );
    v___x_2738_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2739_ = lean_array_push(v___x_2738_, v___x_2737_);
    return v___x_2739_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24()
-> *mut LeanObject {
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    v___x_2740_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__23,
    );
    v___x_2741_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__9;
    v___x_2742_ = lean_box(2);
    v___x_2743_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2743_, 0, v___x_2742_);
    lean_ctor_set(v___x_2743_, 1, v___x_2741_);
    lean_ctor_set(v___x_2743_, 2, v___x_2740_);
    return v___x_2743_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25()
-> *mut LeanObject {
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    v___x_2744_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__24,
    );
    v___x_2745_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2746_ = lean_array_push(v___x_2745_, v___x_2744_);
    return v___x_2746_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26()
-> *mut LeanObject {
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    v___x_2747_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__25,
    );
    v___x_2748_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__7;
    v___x_2749_ = lean_box(2);
    v___x_2750_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2750_, 0, v___x_2749_);
    lean_ctor_set(v___x_2750_, 1, v___x_2748_);
    lean_ctor_set(v___x_2750_, 2, v___x_2747_);
    return v___x_2750_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27()
-> *mut LeanObject {
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    v___x_2751_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__26,
    );
    v___x_2752_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__5;
    v___x_2753_ = lean_array_push(v___x_2752_, v___x_2751_);
    return v___x_2753_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28()
-> *mut LeanObject {
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    v___x_2754_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__27,
    );
    v___x_2755_ = l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__4;
    v___x_2756_ = lean_box(2);
    v___x_2757_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_2757_, 0, v___x_2756_);
    lean_ctor_set(v___x_2757_, 1, v___x_2755_);
    lean_ctor_set(v___x_2757_, 2, v___x_2754_);
    return v___x_2757_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam() -> *mut LeanObject {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    v___x_2758_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28,
    );
    return v___x_2758_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(
    mut v_x_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1;
    v___x_2767_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2767_, 0, v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___boxed(
    mut v_x_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2772_: *mut LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0(
        v_x_2768_,
        v___y_2769_,
        v___y_2770_,
    );
    lean_dec_ref(v___y_2770_);
    lean_dec(v___y_2769_);
    lean_dec(v_x_2768_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(
    mut v_inst_2773_: *mut LeanObject,
    mut v_x_2774_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_2773_);
    return v_inst_2773_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed(
    mut v_inst_2775_: *mut LeanObject,
    mut v_x_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2777_: *mut LeanObject = core::ptr::null_mut();
    v_res_2777_ =
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1(v_inst_2775_, v_x_2776_);
    lean_dec(v_x_2776_);
    lean_dec(v_inst_2775_);
    return v_res_2777_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(
    mut v_s_2778_: *mut LeanObject,
    mut v_x_2779_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_s_2778_);
    return v_s_2778_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2___boxed(
    mut v_s_2780_: *mut LeanObject,
    mut v_x_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2782_: *mut LeanObject = core::ptr::null_mut();
    v_res_2782_ =
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__2(v_s_2780_, v_x_2781_);
    lean_dec(v_x_2781_);
    lean_dec(v_s_2780_);
    return v_res_2782_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(
    mut v_x_2783_: *mut LeanObject,
    mut v_a_2784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    v___x_2785_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2785_, 0, v_a_2784_);
    lean_inc_ref_n(v___x_2785_, 2);
    v___x_2786_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2786_, 0, v___x_2785_);
    lean_ctor_set(v___x_2786_, 1, v___x_2785_);
    lean_ctor_set(v___x_2786_, 2, v___x_2785_);
    return v___x_2786_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3___boxed(
    mut v_x_2787_: *mut LeanObject,
    mut v_a_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2789_: *mut LeanObject = core::ptr::null_mut();
    v_res_2789_ =
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__3(v_x_2787_, v_a_2788_);
    lean_dec_ref(v_x_2787_);
    return v_res_2789_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    v___x_2793_ = l_instInhabitedError;
    v___x_2794_ = lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_2794_, 0, lean_box(0));
    lean_closure_set(v___x_2794_, 1, lean_box(0));
    lean_closure_set(v___x_2794_, 2, v___x_2793_);
    return v___x_2794_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(
    mut v_inst_2796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    v___f_2797_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0;
    v___f_2798_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2798_, 0, v_inst_2796_);
    v___f_2799_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1;
    v___f_2800_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2;
    v___x_2801_ = lean_box(0);
    v___x_2802_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3,
    );
    v___x_2803_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4;
    v___x_2804_ = lean_alloc_ctor(0, 7, (0) as u32);
    lean_ctor_set(v___x_2804_, 0, v___x_2801_);
    lean_ctor_set(v___x_2804_, 1, v___x_2802_);
    lean_ctor_set(v___x_2804_, 2, v___f_2797_);
    lean_ctor_set(v___x_2804_, 3, v___f_2798_);
    lean_ctor_set(v___x_2804_, 4, v___f_2799_);
    lean_ctor_set(v___x_2804_, 5, v___x_2803_);
    lean_ctor_set(v___x_2804_, 6, v___f_2800_);
    return v___x_2804_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_instInhabitedDescr(
    mut v_00_u03b1_2805_: *mut LeanObject,
    mut v_00_u03b2_2806_: *mut LeanObject,
    mut v_00_u03c3_2807_: *mut LeanObject,
    mut v_inst_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    v___x_2809_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg(v_inst_2808_);
    return v___x_2809_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial___redArg(
    mut v_descr_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mkInitial_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2817_: u8 = 0;
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mkInitial_2812_ = lean_ctor_get(v_descr_2810_, 1);
                lean_inc_ref(v_mkInitial_2812_);
                lean_dec_ref(v_descr_2810_);
                v___x_2813_ = lean_apply_1(v_mkInitial_2812_, lean_box(0));
                if lean_obj_tag(v___x_2813_) == 0 {
                    v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
                    v_isSharedCheck_2828_ = (!lean_is_exclusive(v___x_2813_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2816_ = v___x_2813_;
                        v_isShared_2817_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2814_);
                        lean_dec(v___x_2813_);
                        v___x_2816_ = lean_box(0);
                        v_isShared_2817_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2829_ = lean_ctor_get(v___x_2813_, 0);
                    v_isSharedCheck_2836_ = (!lean_is_exclusive(v___x_2813_)) as u8;
                    if v_isSharedCheck_2836_ == 0 {
                        v___x_2831_ = v___x_2813_;
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2829_);
                        lean_dec(v___x_2813_);
                        v___x_2831_ = lean_box(0);
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2818_ = l_Lean_NameSet_empty;
                v___x_2819_ = 1;
                v___x_2820_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2820_, 0, v_a_2814_);
                lean_ctor_set(v___x_2820_, 1, v___x_2818_);
                lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2819_,
                );
                v___x_2821_ = lean_box(0);
                v___x_2822_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2822_, 0, v___x_2820_);
                lean_ctor_set(v___x_2822_, 1, v___x_2821_);
                v___x_2823_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once), _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
                v___x_2824_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2824_, 0, v___x_2822_);
                lean_ctor_set(v___x_2824_, 1, v___x_2823_);
                lean_ctor_set(v___x_2824_, 2, v___x_2821_);
                if v_isShared_2817_ == 0 {
                    lean_ctor_set(v___x_2816_, 0, v___x_2824_);
                    v___x_2826_ = v___x_2816_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
                    v___x_2826_ = v_reuseFailAlloc_2827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2826_;
            }
            3 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial___redArg___boxed(
    mut v_descr_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2839_: *mut LeanObject = core::ptr::null_mut();
    v_res_2839_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_2837_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial(
    mut v_00_u03b1_2840_: *mut LeanObject,
    mut v_00_u03b2_2841_: *mut LeanObject,
    mut v_00_u03c3_2842_: *mut LeanObject,
    mut v_descr_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    v___x_2845_ = l_Lean_ScopedEnvExtension_mkInitial___redArg(v_descr_2843_);
    return v___x_2845_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_mkInitial___boxed(
    mut v_00_u03b1_2846_: *mut LeanObject,
    mut v_00_u03b2_2847_: *mut LeanObject,
    mut v_00_u03c3_2848_: *mut LeanObject,
    mut v_descr_2849_: *mut LeanObject,
    mut v_a_2850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2851_: *mut LeanObject = core::ptr::null_mut();
    v_res_2851_ = l_Lean_ScopedEnvExtension_mkInitial(
        v_00_u03b1_2846_,
        v_00_u03b2_2847_,
        v_00_u03c3_2848_,
        v_descr_2849_,
    );
    return v_res_2851_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(
    mut v_a_2852_: *mut LeanObject,
    mut v_x_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2853_) == 0 {
                    v___x_2854_ = lean_box(0);
                    return v___x_2854_;
                } else {
                    v_key_2855_ = lean_ctor_get(v_x_2853_, 0);
                    v_value_2856_ = lean_ctor_get(v_x_2853_, 1);
                    v_tail_2857_ = lean_ctor_get(v_x_2853_, 2);
                    v___x_2858_ = lean_name_eq(v_key_2855_, v_a_2852_);
                    if v___x_2858_ == 0 {
                        v_x_2853_ = v_tail_2857_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2856_);
                        v___x_2860_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2860_, 0, v_value_2856_);
                        return v___x_2860_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_2861_: *mut LeanObject,
    mut v_x_2862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2863_: *mut LeanObject = core::ptr::null_mut();
    v_res_2863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_2861_, v_x_2862_);
    lean_dec(v_x_2862_);
    lean_dec(v_a_2861_);
    return v_res_2863_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u64 = 0;
    v___x_2864_ = lean_unsigned_to_nat(1723);
    v___x_2865_ = lean_uint64_of_nat(v___x_2864_);
    return v___x_2865_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(
    mut v_m_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2871_: u64 = 0;
    let mut v___x_2872_: u64 = 0;
    let mut v___x_2873_: u64 = 0;
    let mut v_fold_2874_: u64 = 0;
    let mut v___x_2875_: u64 = 0;
    let mut v___x_2876_: u64 = 0;
    let mut v___x_2877_: u64 = 0;
    let mut v___x_2878_: usize = 0;
    let mut v___x_2879_: usize = 0;
    let mut v___x_2880_: usize = 0;
    let mut v___x_2881_: usize = 0;
    let mut v___x_2882_: usize = 0;
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u64 = 0;
    let mut v_hash_2886_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2868_ = lean_ctor_get(v_m_2866_, 1);
                v___x_2869_ = lean_array_get_size(v_buckets_2868_);
                if lean_obj_tag(v_a_2867_) == 0 {
                    v___x_2885_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_2871_ = v___x_2885_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2886_ = lean_ctor_get_uint64(
                        v_a_2867_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2871_ = v_hash_2886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2872_ = 32u64;
                v___x_2873_ = lean_uint64_shift_right(v___y_2871_, v___x_2872_);
                v_fold_2874_ = lean_uint64_xor(v___y_2871_, v___x_2873_);
                v___x_2875_ = 16u64;
                v___x_2876_ = lean_uint64_shift_right(v_fold_2874_, v___x_2875_);
                v___x_2877_ = lean_uint64_xor(v_fold_2874_, v___x_2876_);
                v___x_2878_ = lean_uint64_to_usize(v___x_2877_);
                v___x_2879_ = lean_usize_of_nat(v___x_2869_);
                v___x_2880_ = 1usize;
                v___x_2881_ = lean_usize_sub(v___x_2879_, v___x_2880_);
                v___x_2882_ = lean_usize_land(v___x_2878_, v___x_2881_);
                v___x_2883_ = lean_array_uget_borrowed(v_buckets_2868_, v___x_2882_);
                v___x_2884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_2867_, v___x_2883_);
                return v___x_2884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___boxed(
    mut v_m_2887_: *mut LeanObject,
    mut v_a_2888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2889_: *mut LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_2887_, v_a_2888_);
    lean_dec(v_a_2888_);
    lean_dec_ref(v_m_2887_);
    return v_res_2889_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_2890_: *mut LeanObject,
    mut v_vals_2891_: *mut LeanObject,
    mut v_i_2892_: *mut LeanObject,
    mut v_k_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2894_ = lean_array_get_size(v_keys_2890_);
                v___x_2895_ = lean_nat_dec_lt(v_i_2892_, v___x_2894_);
                if v___x_2895_ == 0 {
                    lean_dec(v_i_2892_);
                    v___x_2896_ = lean_box(0);
                    return v___x_2896_;
                } else {
                    v_k_x27_2897_ = lean_array_fget_borrowed(v_keys_2890_, v_i_2892_);
                    v___x_2898_ = lean_name_eq(v_k_2893_, v_k_x27_2897_);
                    if v___x_2898_ == 0 {
                        v___x_2899_ = lean_unsigned_to_nat(1);
                        v___x_2900_ = lean_nat_add(v_i_2892_, v___x_2899_);
                        lean_dec(v_i_2892_);
                        v_i_2892_ = v___x_2900_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2902_ = lean_array_fget_borrowed(v_vals_2891_, v_i_2892_);
                        lean_dec(v_i_2892_);
                        lean_inc(v___x_2902_);
                        v___x_2903_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2903_, 0, v___x_2902_);
                        return v___x_2903_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_2904_: *mut LeanObject,
    mut v_vals_2905_: *mut LeanObject,
    mut v_i_2906_: *mut LeanObject,
    mut v_k_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2908_: *mut LeanObject = core::ptr::null_mut();
    v_res_2908_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2904_, v_vals_2905_, v_i_2906_, v_k_2907_);
    lean_dec(v_k_2907_);
    lean_dec_ref(v_vals_2905_);
    lean_dec_ref(v_keys_2904_);
    return v_res_2908_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2909_: usize = 0;
    let mut v___x_2910_: usize = 0;
    let mut v___x_2911_: usize = 0;
    v___x_2909_ = 5usize;
    v___x_2910_ = 1usize;
    v___x_2911_ = lean_usize_shift_left(v___x_2910_, v___x_2909_);
    return v___x_2911_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2912_: usize = 0;
    let mut v___x_2913_: usize = 0;
    let mut v___x_2914_: usize = 0;
    v___x_2912_ = 1usize;
    v___x_2913_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2914_ = lean_usize_sub(v___x_2913_, v___x_2912_);
    return v___x_2914_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(
    mut v_x_2915_: *mut LeanObject,
    mut v_x_2916_: usize,
    mut v_x_2917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: usize = 0;
    let mut v___x_2921_: usize = 0;
    let mut v___x_2922_: usize = 0;
    let mut v_j_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: usize = 0;
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2915_) == 0 {
                    v_es_2918_ = lean_ctor_get(v_x_2915_, 0);
                    v___x_2919_ = lean_box(2);
                    v___x_2920_ = 5usize;
                    v___x_2921_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2922_ = lean_usize_land(v_x_2916_, v___x_2921_);
                    v_j_2923_ = lean_usize_to_nat(v___x_2922_);
                    v___x_2924_ = lean_array_get_borrowed(v___x_2919_, v_es_2918_, v_j_2923_);
                    lean_dec(v_j_2923_);
                    match lean_obj_tag(v___x_2924_) {
                        0 => {
                            v_key_2925_ = lean_ctor_get(v___x_2924_, 0);
                            v_val_2926_ = lean_ctor_get(v___x_2924_, 1);
                            v___x_2927_ = lean_name_eq(v_x_2917_, v_key_2925_);
                            if v___x_2927_ == 0 {
                                v___x_2928_ = lean_box(0);
                                return v___x_2928_;
                            } else {
                                lean_inc(v_val_2926_);
                                v___x_2929_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2929_, 0, v_val_2926_);
                                return v___x_2929_;
                            }
                        }
                        1 => {
                            v_node_2930_ = lean_ctor_get(v___x_2924_, 0);
                            v___x_2931_ = lean_usize_shift_right(v_x_2916_, v___x_2920_);
                            v_x_2915_ = v_node_2930_;
                            v_x_2916_ = v___x_2931_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2933_ = lean_box(0);
                            return v___x_2933_;
                        }
                    }
                } else {
                    v_ks_2934_ = lean_ctor_get(v_x_2915_, 0);
                    v_vs_2935_ = lean_ctor_get(v_x_2915_, 1);
                    v___x_2936_ = lean_unsigned_to_nat(0);
                    v___x_2937_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2934_, v_vs_2935_, v___x_2936_, v_x_2917_);
                    return v___x_2937_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2938_: *mut LeanObject,
    mut v_x_2939_: *mut LeanObject,
    mut v_x_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1076__boxed_2941_: usize = 0;
    let mut v_res_2942_: *mut LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_2941_ = lean_unbox_usize(v_x_2939_);
    lean_dec(v_x_2939_);
    v_res_2942_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_2938_, v_x_1076__boxed_2941_, v_x_2940_);
    lean_dec(v_x_2940_);
    lean_dec_ref(v_x_2938_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(
    mut v_x_2943_: *mut LeanObject,
    mut v_x_2944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2946_: u64 = 0;
    let mut v___x_2947_: usize = 0;
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: u64 = 0;
    let mut v_hash_2950_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2944_) == 0 {
                    v___x_2949_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_2946_ = v___x_2949_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2950_ = lean_ctor_get_uint64(
                        v_x_2944_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2946_ = v_hash_2950_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2947_ = lean_uint64_to_usize(v___y_2946_);
                v___x_2948_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_2943_, v___x_2947_, v_x_2944_);
                return v___x_2948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_2951_: *mut LeanObject,
    mut v_x_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2953_: *mut LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_2951_, v_x_2952_);
    lean_dec(v_x_2952_);
    lean_dec_ref(v_x_2951_);
    return v_res_2953_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
    mut v_x_2954_: *mut LeanObject,
    mut v_x_2955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_2956_: u8 = 0;
    v_stage_u2081_2956_ = lean_ctor_get_uint8(
        v_x_2954_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_2956_ == 0 {
        let mut v_map_u2081_2957_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_2958_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_2957_ = lean_ctor_get(v_x_2954_, 0);
        v_map_u2082_2958_ = lean_ctor_get(v_x_2954_, 1);
        v___x_2959_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_map_u2082_2958_, v_x_2955_);
        if lean_obj_tag(v___x_2959_) == 0 {
            let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
            v___x_2960_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_2957_, v_x_2955_);
            return v___x_2960_;
        } else {
            return v___x_2959_;
        }
    } else {
        let mut v_map_u2081_2961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_2961_ = lean_ctor_get(v_x_2954_, 0);
        v___x_2962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_map_u2081_2961_, v_x_2955_);
        return v___x_2962_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg___boxed(
    mut v_x_2963_: *mut LeanObject,
    mut v_x_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2965_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
            v_x_2963_, v_x_2964_,
        );
    lean_dec(v_x_2964_);
    lean_dec_ref(v_x_2963_);
    return v_res_2965_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(
    mut v_a_2966_: *mut LeanObject,
    mut v_b_2967_: *mut LeanObject,
    mut v_x_2968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2968_) == 0 {
                    lean_dec(v_b_2967_);
                    lean_dec(v_a_2966_);
                    return v_x_2968_;
                } else {
                    v_key_2969_ = lean_ctor_get(v_x_2968_, 0);
                    v_value_2970_ = lean_ctor_get(v_x_2968_, 1);
                    v_tail_2971_ = lean_ctor_get(v_x_2968_, 2);
                    v_isSharedCheck_2983_ = (!lean_is_exclusive(v_x_2968_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v___x_2973_ = v_x_2968_;
                        v_isShared_2974_ = v_isSharedCheck_2983_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2971_);
                        lean_inc(v_value_2970_);
                        lean_inc(v_key_2969_);
                        lean_dec(v_x_2968_);
                        v___x_2973_ = lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_2983_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2975_ = lean_name_eq(v_key_2969_, v_a_2966_);
                if v___x_2975_ == 0 {
                    v___x_2976_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_2966_, v_b_2967_, v_tail_2971_);
                    if v_isShared_2974_ == 0 {
                        lean_ctor_set(v___x_2973_, 2, v___x_2976_);
                        v___x_2978_ = v___x_2973_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_key_2969_);
                        lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_value_2970_);
                        lean_ctor_set(v_reuseFailAlloc_2979_, 2, v___x_2976_);
                        v___x_2978_ = v_reuseFailAlloc_2979_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2970_);
                    lean_dec(v_key_2969_);
                    if v_isShared_2974_ == 0 {
                        lean_ctor_set(v___x_2973_, 1, v_b_2967_);
                        lean_ctor_set(v___x_2973_, 0, v_a_2966_);
                        v___x_2981_ = v___x_2973_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2966_);
                        lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_b_2967_);
                        lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_tail_2971_);
                        v___x_2981_ = v_reuseFailAlloc_2982_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2978_;
            }
            3 => {
                return v___x_2981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(
    mut v_x_2984_: *mut LeanObject,
    mut v_x_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2994_: u64 = 0;
    let mut v___x_2995_: u64 = 0;
    let mut v___x_2996_: u64 = 0;
    let mut v_fold_2997_: u64 = 0;
    let mut v___x_2998_: u64 = 0;
    let mut v___x_2999_: u64 = 0;
    let mut v___x_3000_: u64 = 0;
    let mut v___x_3001_: usize = 0;
    let mut v___x_3002_: usize = 0;
    let mut v___x_3003_: usize = 0;
    let mut v___x_3004_: usize = 0;
    let mut v___x_3005_: usize = 0;
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u64 = 0;
    let mut v_hash_3013_: u64 = 0;
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2985_) == 0 {
                    return v_x_2984_;
                } else {
                    v_key_2986_ = lean_ctor_get(v_x_2985_, 0);
                    v_value_2987_ = lean_ctor_get(v_x_2985_, 1);
                    v_tail_2988_ = lean_ctor_get(v_x_2985_, 2);
                    v_isSharedCheck_3014_ = (!lean_is_exclusive(v_x_2985_)) as u8;
                    if v_isSharedCheck_3014_ == 0 {
                        v___x_2990_ = v_x_2985_;
                        v_isShared_2991_ = v_isSharedCheck_3014_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2988_);
                        lean_inc(v_value_2987_);
                        lean_inc(v_key_2986_);
                        lean_dec(v_x_2985_);
                        v___x_2990_ = lean_box(0);
                        v_isShared_2991_ = v_isSharedCheck_3014_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2992_ = lean_array_get_size(v_x_2984_);
                if lean_obj_tag(v_key_2986_) == 0 {
                    v___x_3012_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_2994_ = v___x_3012_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3013_ = lean_ctor_get_uint64(
                        v_key_2986_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2994_ = v_hash_3013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2995_ = 32u64;
                v___x_2996_ = lean_uint64_shift_right(v___y_2994_, v___x_2995_);
                v_fold_2997_ = lean_uint64_xor(v___y_2994_, v___x_2996_);
                v___x_2998_ = 16u64;
                v___x_2999_ = lean_uint64_shift_right(v_fold_2997_, v___x_2998_);
                v___x_3000_ = lean_uint64_xor(v_fold_2997_, v___x_2999_);
                v___x_3001_ = lean_uint64_to_usize(v___x_3000_);
                v___x_3002_ = lean_usize_of_nat(v___x_2992_);
                v___x_3003_ = 1usize;
                v___x_3004_ = lean_usize_sub(v___x_3002_, v___x_3003_);
                v___x_3005_ = lean_usize_land(v___x_3001_, v___x_3004_);
                v___x_3006_ = lean_array_uget_borrowed(v_x_2984_, v___x_3005_);
                lean_inc(v___x_3006_);
                if v_isShared_2991_ == 0 {
                    lean_ctor_set(v___x_2990_, 2, v___x_3006_);
                    v___x_3008_ = v___x_2990_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_key_2986_);
                    lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_value_2987_);
                    lean_ctor_set(v_reuseFailAlloc_3011_, 2, v___x_3006_);
                    v___x_3008_ = v_reuseFailAlloc_3011_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3009_ = lean_array_uset(v_x_2984_, v___x_3005_, v___x_3008_);
                v_x_2984_ = v___x_3009_;
                v_x_2985_ = v_tail_2988_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(
    mut v_i_3015_: *mut LeanObject,
    mut v_source_3016_: *mut LeanObject,
    mut v_target_3017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v_es_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3018_ = lean_array_get_size(v_source_3016_);
                v___x_3019_ = lean_nat_dec_lt(v_i_3015_, v___x_3018_);
                if v___x_3019_ == 0 {
                    lean_dec_ref(v_source_3016_);
                    lean_dec(v_i_3015_);
                    return v_target_3017_;
                } else {
                    v_es_3020_ = lean_array_fget(v_source_3016_, v_i_3015_);
                    v___x_3021_ = lean_box(0);
                    v_source_3022_ = lean_array_fset(v_source_3016_, v_i_3015_, v___x_3021_);
                    v_target_3023_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_target_3017_, v_es_3020_);
                    v___x_3024_ = lean_unsigned_to_nat(1);
                    v___x_3025_ = lean_nat_add(v_i_3015_, v___x_3024_);
                    lean_dec(v_i_3015_);
                    v_i_3015_ = v___x_3025_;
                    v_source_3016_ = v_source_3022_;
                    v_target_3017_ = v_target_3023_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(
    mut v_data_3027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    v___x_3028_ = lean_array_get_size(v_data_3027_);
    v___x_3029_ = lean_unsigned_to_nat(2);
    v_nbuckets_3030_ = lean_nat_mul(v___x_3028_, v___x_3029_);
    v___x_3031_ = lean_unsigned_to_nat(0);
    v___x_3032_ = lean_box(0);
    v___x_3033_ = lean_mk_array(v_nbuckets_3030_, v___x_3032_);
    v___x_3034_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v___x_3031_, v_data_3027_, v___x_3033_);
    return v___x_3034_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(
    mut v_a_3035_: *mut LeanObject,
    mut v_x_3036_: *mut LeanObject,
) -> u8 {
    let mut v___x_3037_: u8 = 0;
    let mut v_key_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3036_) == 0 {
                    v___x_3037_ = 0;
                    return v___x_3037_;
                } else {
                    v_key_3038_ = lean_ctor_get(v_x_3036_, 0);
                    v_tail_3039_ = lean_ctor_get(v_x_3036_, 2);
                    v___x_3040_ = lean_name_eq(v_key_3038_, v_a_3035_);
                    if v___x_3040_ == 0 {
                        v_x_3036_ = v_tail_3039_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3040_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg___boxed(
    mut v_a_3042_: *mut LeanObject,
    mut v_x_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3044_: u8 = 0;
    let mut v_r_3045_: *mut LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_3042_, v_x_3043_);
    lean_dec(v_x_3043_);
    lean_dec(v_a_3042_);
    v_r_3045_ = lean_box((v_res_3044_) as usize);
    return v_r_3045_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(
    mut v_m_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
    mut v_b_3048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: u64 = 0;
    let mut v___x_3057_: u64 = 0;
    let mut v___x_3058_: u64 = 0;
    let mut v_fold_3059_: u64 = 0;
    let mut v___x_3060_: u64 = 0;
    let mut v___x_3061_: u64 = 0;
    let mut v___x_3062_: u64 = 0;
    let mut v___x_3063_: usize = 0;
    let mut v___x_3064_: usize = 0;
    let mut v___x_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v___x_3067_: usize = 0;
    let mut v_bkt_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v_val_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u64 = 0;
    let mut v_hash_3095_: u64 = 0;
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3049_ = lean_ctor_get(v_m_3046_, 0);
                v_buckets_3050_ = lean_ctor_get(v_m_3046_, 1);
                v_isSharedCheck_3096_ = (!lean_is_exclusive(v_m_3046_)) as u8;
                if v_isSharedCheck_3096_ == 0 {
                    v___x_3052_ = v_m_3046_;
                    v_isShared_3053_ = v_isSharedCheck_3096_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3050_);
                    lean_inc(v_size_3049_);
                    lean_dec(v_m_3046_);
                    v___x_3052_ = lean_box(0);
                    v_isShared_3053_ = v_isSharedCheck_3096_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3054_ = lean_array_get_size(v_buckets_3050_);
                if lean_obj_tag(v_a_3047_) == 0 {
                    v___x_3094_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_3056_ = v___x_3094_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3095_ = lean_ctor_get_uint64(
                        v_a_3047_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3056_ = v_hash_3095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3057_ = 32u64;
                v___x_3058_ = lean_uint64_shift_right(v___y_3056_, v___x_3057_);
                v_fold_3059_ = lean_uint64_xor(v___y_3056_, v___x_3058_);
                v___x_3060_ = 16u64;
                v___x_3061_ = lean_uint64_shift_right(v_fold_3059_, v___x_3060_);
                v___x_3062_ = lean_uint64_xor(v_fold_3059_, v___x_3061_);
                v___x_3063_ = lean_uint64_to_usize(v___x_3062_);
                v___x_3064_ = lean_usize_of_nat(v___x_3054_);
                v___x_3065_ = 1usize;
                v___x_3066_ = lean_usize_sub(v___x_3064_, v___x_3065_);
                v___x_3067_ = lean_usize_land(v___x_3063_, v___x_3066_);
                v_bkt_3068_ = lean_array_uget_borrowed(v_buckets_3050_, v___x_3067_);
                v___x_3069_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_3047_, v_bkt_3068_);
                if v___x_3069_ == 0 {
                    v___x_3070_ = lean_unsigned_to_nat(1);
                    v_size_x27_3071_ = lean_nat_add(v_size_3049_, v___x_3070_);
                    lean_dec(v_size_3049_);
                    lean_inc(v_bkt_3068_);
                    v___x_3072_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3072_, 0, v_a_3047_);
                    lean_ctor_set(v___x_3072_, 1, v_b_3048_);
                    lean_ctor_set(v___x_3072_, 2, v_bkt_3068_);
                    v_buckets_x27_3073_ =
                        lean_array_uset(v_buckets_3050_, v___x_3067_, v___x_3072_);
                    v___x_3074_ = lean_unsigned_to_nat(4);
                    v___x_3075_ = lean_nat_mul(v_size_x27_3071_, v___x_3074_);
                    v___x_3076_ = lean_unsigned_to_nat(3);
                    v___x_3077_ = lean_nat_div(v___x_3075_, v___x_3076_);
                    lean_dec(v___x_3075_);
                    v___x_3078_ = lean_array_get_size(v_buckets_x27_3073_);
                    v___x_3079_ = lean_nat_dec_le(v___x_3077_, v___x_3078_);
                    lean_dec(v___x_3077_);
                    if v___x_3079_ == 0 {
                        v_val_3080_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_buckets_x27_3073_);
                        if v_isShared_3053_ == 0 {
                            lean_ctor_set(v___x_3052_, 1, v_val_3080_);
                            lean_ctor_set(v___x_3052_, 0, v_size_x27_3071_);
                            v___x_3082_ = v___x_3052_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_size_x27_3071_);
                            lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_val_3080_);
                            v___x_3082_ = v_reuseFailAlloc_3083_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3053_ == 0 {
                            lean_ctor_set(v___x_3052_, 1, v_buckets_x27_3073_);
                            lean_ctor_set(v___x_3052_, 0, v_size_x27_3071_);
                            v___x_3085_ = v___x_3052_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_size_x27_3071_);
                            lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_buckets_x27_3073_);
                            v___x_3085_ = v_reuseFailAlloc_3086_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3068_);
                    v___x_3087_ = lean_box(0);
                    v_buckets_x27_3088_ =
                        lean_array_uset(v_buckets_3050_, v___x_3067_, v___x_3087_);
                    v___x_3089_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_3047_, v_b_3048_, v_bkt_3068_);
                    v___x_3090_ = lean_array_uset(v_buckets_x27_3088_, v___x_3067_, v___x_3089_);
                    if v_isShared_3053_ == 0 {
                        lean_ctor_set(v___x_3052_, 1, v___x_3090_);
                        v___x_3092_ = v___x_3052_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_size_3049_);
                        lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3090_);
                        v___x_3092_ = v_reuseFailAlloc_3093_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3082_;
            }
            4 => {
                return v___x_3085_;
            }
            5 => {
                return v___x_3092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(
    mut v_x_3097_: *mut LeanObject,
    mut v_x_3098_: *mut LeanObject,
    mut v_x_3099_: *mut LeanObject,
    mut v_x_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3101_ = lean_ctor_get(v_x_3097_, 0);
                v_vs_3102_ = lean_ctor_get(v_x_3097_, 1);
                v_isSharedCheck_3126_ = (!lean_is_exclusive(v_x_3097_)) as u8;
                if v_isSharedCheck_3126_ == 0 {
                    v___x_3104_ = v_x_3097_;
                    v_isShared_3105_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3102_);
                    lean_inc(v_ks_3101_);
                    lean_dec(v_x_3097_);
                    v___x_3104_ = lean_box(0);
                    v_isShared_3105_ = v_isSharedCheck_3126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3106_ = lean_array_get_size(v_ks_3101_);
                v___x_3107_ = lean_nat_dec_lt(v_x_3098_, v___x_3106_);
                if v___x_3107_ == 0 {
                    lean_dec(v_x_3098_);
                    v___x_3108_ = lean_array_push(v_ks_3101_, v_x_3099_);
                    v___x_3109_ = lean_array_push(v_vs_3102_, v_x_3100_);
                    if v_isShared_3105_ == 0 {
                        lean_ctor_set(v___x_3104_, 1, v___x_3109_);
                        lean_ctor_set(v___x_3104_, 0, v___x_3108_);
                        v___x_3111_ = v___x_3104_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3108_);
                        lean_ctor_set(v_reuseFailAlloc_3112_, 1, v___x_3109_);
                        v___x_3111_ = v_reuseFailAlloc_3112_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3113_ = lean_array_fget_borrowed(v_ks_3101_, v_x_3098_);
                    v___x_3114_ = lean_name_eq(v_x_3099_, v_k_x27_3113_);
                    if v___x_3114_ == 0 {
                        if v_isShared_3105_ == 0 {
                            v___x_3116_ = v___x_3104_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_ks_3101_);
                            lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_vs_3102_);
                            v___x_3116_ = v_reuseFailAlloc_3120_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3121_ = lean_array_fset(v_ks_3101_, v_x_3098_, v_x_3099_);
                        v___x_3122_ = lean_array_fset(v_vs_3102_, v_x_3098_, v_x_3100_);
                        lean_dec(v_x_3098_);
                        if v_isShared_3105_ == 0 {
                            lean_ctor_set(v___x_3104_, 1, v___x_3122_);
                            lean_ctor_set(v___x_3104_, 0, v___x_3121_);
                            v___x_3124_ = v___x_3104_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3121_);
                            lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3122_);
                            v___x_3124_ = v_reuseFailAlloc_3125_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3111_;
            }
            3 => {
                v___x_3117_ = lean_unsigned_to_nat(1);
                v___x_3118_ = lean_nat_add(v_x_3098_, v___x_3117_);
                lean_dec(v_x_3098_);
                v_x_3097_ = v___x_3116_;
                v_x_3098_ = v___x_3118_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(
    mut v_n_3127_: *mut LeanObject,
    mut v_k_3128_: *mut LeanObject,
    mut v_v_3129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    v___x_3130_ = lean_unsigned_to_nat(0);
    v___x_3131_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_n_3127_, v___x_3130_, v_k_3128_, v_v_3129_);
    return v___x_3131_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3132_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(
    mut v_x_3133_: *mut LeanObject,
    mut v_x_3134_: usize,
    mut v_x_3135_: usize,
    mut v_x_3136_: *mut LeanObject,
    mut v_x_3137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: usize = 0;
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: usize = 0;
    let mut v___x_3142_: usize = 0;
    let mut v_j_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v_v_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3162_: u8 = 0;
    let mut v___x_3163_: u8 = 0;
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3169_: u8 = 0;
    let mut v_node_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: usize = 0;
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_unused_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3193_: u8 = 0;
    let mut v_ks_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: usize = 0;
    let mut v___x_3200_: u8 = 0;
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3133_) == 0 {
                    v_es_3138_ = lean_ctor_get(v_x_3133_, 0);
                    v___x_3139_ = 5usize;
                    v___x_3140_ = 1usize;
                    v___x_3141_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3142_ = lean_usize_land(v_x_3134_, v___x_3141_);
                    v_j_3143_ = lean_usize_to_nat(v___x_3142_);
                    v___x_3144_ = lean_array_get_size(v_es_3138_);
                    v___x_3145_ = lean_nat_dec_lt(v_j_3143_, v___x_3144_);
                    if v___x_3145_ == 0 {
                        lean_dec(v_j_3143_);
                        lean_dec(v_x_3137_);
                        lean_dec(v_x_3136_);
                        return v_x_3133_;
                    } else {
                        lean_inc_ref(v_es_3138_);
                        v_isSharedCheck_3182_ = (!lean_is_exclusive(v_x_3133_)) as u8;
                        if v_isSharedCheck_3182_ == 0 {
                            v_unused_3183_ = lean_ctor_get(v_x_3133_, 0);
                            lean_dec(v_unused_3183_);
                            v___x_3147_ = v_x_3133_;
                            v_isShared_3148_ = v_isSharedCheck_3182_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3133_);
                            v___x_3147_ = lean_box(0);
                            v_isShared_3148_ = v_isSharedCheck_3182_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3184_ = lean_ctor_get(v_x_3133_, 0);
                    v_vs_3185_ = lean_ctor_get(v_x_3133_, 1);
                    v_isSharedCheck_3205_ = (!lean_is_exclusive(v_x_3133_)) as u8;
                    if v_isSharedCheck_3205_ == 0 {
                        v___x_3187_ = v_x_3133_;
                        v_isShared_3188_ = v_isSharedCheck_3205_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3185_);
                        lean_inc(v_ks_3184_);
                        lean_dec(v_x_3133_);
                        v___x_3187_ = lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3205_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3149_ = lean_array_fget(v_es_3138_, v_j_3143_);
                v___x_3150_ = lean_box(0);
                v_xs_x27_3151_ = lean_array_fset(v_es_3138_, v_j_3143_, v___x_3150_);
                match lean_obj_tag(v_v_3149_) {
                    0 => {
                        v_key_3158_ = lean_ctor_get(v_v_3149_, 0);
                        v_val_3159_ = lean_ctor_get(v_v_3149_, 1);
                        v_isSharedCheck_3169_ = (!lean_is_exclusive(v_v_3149_)) as u8;
                        if v_isSharedCheck_3169_ == 0 {
                            v___x_3161_ = v_v_3149_;
                            v_isShared_3162_ = v_isSharedCheck_3169_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3159_);
                            lean_inc(v_key_3158_);
                            lean_dec(v_v_3149_);
                            v___x_3161_ = lean_box(0);
                            v_isShared_3162_ = v_isSharedCheck_3169_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3170_ = lean_ctor_get(v_v_3149_, 0);
                        v_isSharedCheck_3180_ = (!lean_is_exclusive(v_v_3149_)) as u8;
                        if v_isSharedCheck_3180_ == 0 {
                            v___x_3172_ = v_v_3149_;
                            v_isShared_3173_ = v_isSharedCheck_3180_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3170_);
                            lean_dec(v_v_3149_);
                            v___x_3172_ = lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3180_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3181_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3181_, 0, v_x_3136_);
                        lean_ctor_set(v___x_3181_, 1, v_x_3137_);
                        v___y_3153_ = v___x_3181_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3154_ = lean_array_fset(v_xs_x27_3151_, v_j_3143_, v___y_3153_);
                lean_dec(v_j_3143_);
                if v_isShared_3148_ == 0 {
                    lean_ctor_set(v___x_3147_, 0, v___x_3154_);
                    v___x_3156_ = v___x_3147_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3156_;
            }
            4 => {
                v___x_3163_ = lean_name_eq(v_x_3136_, v_key_3158_);
                if v___x_3163_ == 0 {
                    lean_del_object(v___x_3161_);
                    v___x_3164_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3158_,
                        v_val_3159_,
                        v_x_3136_,
                        v_x_3137_,
                    );
                    v___x_3165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3165_, 0, v___x_3164_);
                    v___y_3153_ = v___x_3165_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3159_);
                    lean_dec(v_key_3158_);
                    if v_isShared_3162_ == 0 {
                        lean_ctor_set(v___x_3161_, 1, v_x_3137_);
                        lean_ctor_set(v___x_3161_, 0, v_x_3136_);
                        v___x_3167_ = v___x_3161_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_x_3136_);
                        lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_x_3137_);
                        v___x_3167_ = v_reuseFailAlloc_3168_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3153_ = v___x_3167_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3174_ = lean_usize_shift_right(v_x_3134_, v___x_3139_);
                v___x_3175_ = lean_usize_add(v_x_3135_, v___x_3140_);
                v___x_3176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_node_3170_, v___x_3174_, v___x_3175_, v_x_3136_, v_x_3137_);
                if v_isShared_3173_ == 0 {
                    lean_ctor_set(v___x_3172_, 0, v___x_3176_);
                    v___x_3178_ = v___x_3172_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
                    v___x_3178_ = v_reuseFailAlloc_3179_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3153_ = v___x_3178_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3188_ == 0 {
                    v___x_3190_ = v___x_3187_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_ks_3184_);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_vs_3185_);
                    v___x_3190_ = v_reuseFailAlloc_3204_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v___x_3190_, v_x_3136_, v_x_3137_);
                v___x_3199_ = 7usize;
                v___x_3200_ = lean_usize_dec_le(v___x_3199_, v_x_3135_);
                if v___x_3200_ == 0 {
                    v___x_3201_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3191_);
                    v___x_3202_ = lean_unsigned_to_nat(4);
                    v___x_3203_ = lean_nat_dec_lt(v___x_3201_, v___x_3202_);
                    lean_dec(v___x_3201_);
                    v___y_3193_ = v___x_3203_;
                    state = 10;
                    continue;
                } else {
                    v___y_3193_ = v___x_3200_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3193_ == 0 {
                    v_ks_3194_ = lean_ctor_get(v_newNode_3191_, 0);
                    lean_inc_ref(v_ks_3194_);
                    v_vs_3195_ = lean_ctor_get(v_newNode_3191_, 1);
                    lean_inc_ref(v_vs_3195_);
                    lean_dec_ref(v_newNode_3191_);
                    v___x_3196_ = lean_unsigned_to_nat(0);
                    v___x_3197_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___closed__0);
                    v___x_3198_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_x_3135_, v_ks_3194_, v_vs_3195_, v___x_3196_, v___x_3197_);
                    lean_dec_ref(v_vs_3195_);
                    lean_dec_ref(v_ks_3194_);
                    return v___x_3198_;
                } else {
                    return v_newNode_3191_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(
    mut v_depth_3206_: usize,
    mut v_keys_3207_: *mut LeanObject,
    mut v_vals_3208_: *mut LeanObject,
    mut v_i_3209_: *mut LeanObject,
    mut v_entries_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v_k_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: u64 = 0;
    let mut v_h_3217_: usize = 0;
    let mut v___x_3218_: usize = 0;
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: usize = 0;
    let mut v___x_3221_: usize = 0;
    let mut v___x_3222_: usize = 0;
    let mut v_h_3223_: usize = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u64 = 0;
    let mut v_hash_3228_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3211_ = lean_array_get_size(v_keys_3207_);
                v___x_3212_ = lean_nat_dec_lt(v_i_3209_, v___x_3211_);
                if v___x_3212_ == 0 {
                    lean_dec(v_i_3209_);
                    return v_entries_3210_;
                } else {
                    v_k_3213_ = lean_array_fget_borrowed(v_keys_3207_, v_i_3209_);
                    v_v_3214_ = lean_array_fget_borrowed(v_vals_3208_, v_i_3209_);
                    if lean_obj_tag(v_k_3213_) == 0 {
                        v___x_3227_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                        v___y_3216_ = v___x_3227_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3228_ = lean_ctor_get_uint64(
                            v_k_3213_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_3216_ = v_hash_3228_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3217_ = lean_uint64_to_usize(v___y_3216_);
                v___x_3218_ = 5usize;
                v___x_3219_ = lean_unsigned_to_nat(1);
                v___x_3220_ = 1usize;
                v___x_3221_ = lean_usize_sub(v_depth_3206_, v___x_3220_);
                v___x_3222_ = lean_usize_mul(v___x_3218_, v___x_3221_);
                v_h_3223_ = lean_usize_shift_right(v_h_3217_, v___x_3222_);
                v___x_3224_ = lean_nat_add(v_i_3209_, v___x_3219_);
                lean_dec(v_i_3209_);
                lean_inc(v_v_3214_);
                lean_inc(v_k_3213_);
                v___x_3225_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_entries_3210_, v_h_3223_, v_depth_3206_, v_k_3213_, v_v_3214_);
                v_i_3209_ = v___x_3224_;
                v_entries_3210_ = v___x_3225_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg___boxed(
    mut v_depth_3229_: *mut LeanObject,
    mut v_keys_3230_: *mut LeanObject,
    mut v_vals_3231_: *mut LeanObject,
    mut v_i_3232_: *mut LeanObject,
    mut v_entries_3233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3234_: usize = 0;
    let mut v_res_3235_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3234_ = lean_unbox_usize(v_depth_3229_);
    lean_dec(v_depth_3229_);
    v_res_3235_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_boxed_3234_, v_keys_3230_, v_vals_3231_, v_i_3232_, v_entries_3233_);
    lean_dec_ref(v_vals_3231_);
    lean_dec_ref(v_keys_3230_);
    return v_res_3235_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_3236_: *mut LeanObject,
    mut v_x_3237_: *mut LeanObject,
    mut v_x_3238_: *mut LeanObject,
    mut v_x_3239_: *mut LeanObject,
    mut v_x_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1474__boxed_3241_: usize = 0;
    let mut v_x_1475__boxed_3242_: usize = 0;
    let mut v_res_3243_: *mut LeanObject = core::ptr::null_mut();
    v_x_1474__boxed_3241_ = lean_unbox_usize(v_x_3237_);
    lean_dec(v_x_3237_);
    v_x_1475__boxed_3242_ = lean_unbox_usize(v_x_3238_);
    lean_dec(v_x_3238_);
    v_res_3243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_3236_, v_x_1474__boxed_3241_, v_x_1475__boxed_3242_, v_x_3239_, v_x_3240_);
    return v_res_3243_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(
    mut v_x_3244_: *mut LeanObject,
    mut v_x_3245_: *mut LeanObject,
    mut v_x_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3248_: u64 = 0;
    let mut v___x_3249_: usize = 0;
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u64 = 0;
    let mut v_hash_3253_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3245_) == 0 {
                    v___x_3252_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg___closed__0);
                    v___y_3248_ = v___x_3252_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3253_ = lean_ctor_get_uint64(
                        v_x_3245_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3248_ = v_hash_3253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3249_ = lean_uint64_to_usize(v___y_3248_);
                v___x_3250_ = 1usize;
                v___x_3251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_3244_, v___x_3249_, v___x_3250_, v_x_3245_, v_x_3246_);
                return v___x_3251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(
    mut v_x_3254_: *mut LeanObject,
    mut v_x_3255_: *mut LeanObject,
    mut v_x_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_3257_: u8 = 0;
    let mut v_map_u2081_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3267_: u8 = 0;
    let mut v_map_u2081_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_3257_ = lean_ctor_get_uint8(
                    v_x_3254_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_3257_ == 0 {
                    v_map_u2081_3258_ = lean_ctor_get(v_x_3254_, 0);
                    v_map_u2082_3259_ = lean_ctor_get(v_x_3254_, 1);
                    v_isSharedCheck_3267_ = (!lean_is_exclusive(v_x_3254_)) as u8;
                    if v_isSharedCheck_3267_ == 0 {
                        v___x_3261_ = v_x_3254_;
                        v_isShared_3262_ = v_isSharedCheck_3267_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_3259_);
                        lean_inc(v_map_u2081_3258_);
                        lean_dec(v_x_3254_);
                        v___x_3261_ = lean_box(0);
                        v_isShared_3262_ = v_isSharedCheck_3267_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_3268_ = lean_ctor_get(v_x_3254_, 0);
                    v_map_u2082_3269_ = lean_ctor_get(v_x_3254_, 1);
                    v_isSharedCheck_3277_ = (!lean_is_exclusive(v_x_3254_)) as u8;
                    if v_isSharedCheck_3277_ == 0 {
                        v___x_3271_ = v_x_3254_;
                        v_isShared_3272_ = v_isSharedCheck_3277_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_3269_);
                        lean_inc(v_map_u2081_3268_);
                        lean_dec(v_x_3254_);
                        v___x_3271_ = lean_box(0);
                        v_isShared_3272_ = v_isSharedCheck_3277_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3263_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_map_u2082_3259_, v_x_3255_, v_x_3256_);
                if v_isShared_3262_ == 0 {
                    lean_ctor_set(v___x_3261_, 1, v___x_3263_);
                    v___x_3265_ = v___x_3261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_map_u2081_3258_);
                    lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3266_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_3257_,
                    );
                    v___x_3265_ = v_reuseFailAlloc_3266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3265_;
            }
            3 => {
                v___x_3273_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_map_u2081_3268_, v_x_3255_, v_x_3256_);
                if v_isShared_3272_ == 0 {
                    lean_ctor_set(v___x_3271_, 0, v___x_3273_);
                    v___x_3275_ = v___x_3271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
                    lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_map_u2082_3269_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3276_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_3257_,
                    );
                    v___x_3275_ = v_reuseFailAlloc_3276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    v___x_3278_ = lean_unsigned_to_nat(32);
    v___x_3279_ = lean_mk_empty_array_with_capacity(v___x_3278_);
    v___x_3280_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3280_, 0, v___x_3279_);
    return v___x_3280_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3281_: usize = 0;
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    v___x_3281_ = 5usize;
    v___x_3282_ = lean_unsigned_to_nat(0);
    v___x_3283_ = lean_unsigned_to_nat(32);
    v___x_3284_ = lean_mk_empty_array_with_capacity(v___x_3283_);
    v___x_3285_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0_once
        ),
        _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__0,
    );
    v___x_3286_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3286_, 0, v___x_3285_);
    lean_ctor_set(v___x_3286_, 1, v___x_3284_);
    lean_ctor_set(v___x_3286_, 2, v___x_3282_);
    lean_ctor_set(v___x_3286_, 3, v___x_3282_);
    lean_ctor_set_usize(v___x_3286_, 4, v___x_3281_);
    return v___x_3286_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
    mut v_scopedEntries_3287_: *mut LeanObject,
    mut v_ns_3288_: *mut LeanObject,
    mut v_b_3289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    v___x_3290_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
            v_scopedEntries_3287_,
            v_ns_3288_,
        );
    if lean_obj_tag(v___x_3290_) == 0 {
        let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
        v___x_3291_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1_once
            ),
            _init_l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg___closed__1,
        );
        v___x_3292_ = l_Lean_PersistentArray_push___redArg(v___x_3291_, v_b_3289_);
        v___x_3293_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_3287_, v_ns_3288_, v___x_3292_);
        return v___x_3293_;
    } else {
        let mut v_val_3294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
        v_val_3294_ = lean_ctor_get(v___x_3290_, 0);
        lean_inc(v_val_3294_);
        lean_dec_ref_known(v___x_3290_, 1);
        v___x_3295_ = l_Lean_PersistentArray_push___redArg(v_val_3294_, v_b_3289_);
        v___x_3296_ = l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(v_scopedEntries_3287_, v_ns_3288_, v___x_3295_);
        return v___x_3296_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_ScopedEntries_insert(
    mut v_00_u03b2_3297_: *mut LeanObject,
    mut v_scopedEntries_3298_: *mut LeanObject,
    mut v_ns_3299_: *mut LeanObject,
    mut v_b_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
        v_scopedEntries_3298_,
        v_ns_3299_,
        v_b_3300_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(
    mut v_00_u03b2_3302_: *mut LeanObject,
    mut v_x_3303_: *mut LeanObject,
    mut v_x_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    v___x_3305_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(
            v_x_3303_, v_x_3304_,
        );
    return v___x_3305_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___boxed(
    mut v_00_u03b2_3306_: *mut LeanObject,
    mut v_x_3307_: *mut LeanObject,
    mut v_x_3308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3309_: *mut LeanObject = core::ptr::null_mut();
    v_res_3309_ =
        l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0(
            v_00_u03b2_3306_,
            v_x_3307_,
            v_x_3308_,
        );
    lean_dec(v_x_3308_);
    lean_dec_ref(v_x_3307_);
    return v_res_3309_;
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1(
    mut v_00_u03b2_3310_: *mut LeanObject,
    mut v_x_3311_: *mut LeanObject,
    mut v_x_3312_: *mut LeanObject,
    mut v_x_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ =
        l_Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1___redArg(
            v_x_3311_, v_x_3312_, v_x_3313_,
        );
    return v___x_3314_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(
    mut v_00_u03b2_3315_: *mut LeanObject,
    mut v_x_3316_: *mut LeanObject,
    mut v_x_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    v___x_3318_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___redArg(v_x_3316_, v_x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_3319_: *mut LeanObject,
    mut v_x_3320_: *mut LeanObject,
    mut v_x_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3322_: *mut LeanObject = core::ptr::null_mut();
    v_res_3322_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0(v_00_u03b2_3319_, v_x_3320_, v_x_3321_);
    lean_dec(v_x_3321_);
    lean_dec_ref(v_x_3320_);
    return v_res_3322_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(
    mut v_00_u03b2_3323_: *mut LeanObject,
    mut v_m_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___redArg(v_m_3324_, v_a_3325_);
    return v___x_3326_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1___boxed(
    mut v_00_u03b2_3327_: *mut LeanObject,
    mut v_m_3328_: *mut LeanObject,
    mut v_a_3329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3330_: *mut LeanObject = core::ptr::null_mut();
    v_res_3330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1(v_00_u03b2_3327_, v_m_3328_, v_a_3329_);
    lean_dec(v_a_3329_);
    lean_dec_ref(v_m_3328_);
    return v_res_3330_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3(
    mut v_00_u03b2_3331_: *mut LeanObject,
    mut v_x_3332_: *mut LeanObject,
    mut v_x_3333_: *mut LeanObject,
    mut v_x_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    v___x_3335_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3___redArg(v_x_3332_, v_x_3333_, v_x_3334_);
    return v___x_3335_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4(
    mut v_00_u03b2_3336_: *mut LeanObject,
    mut v_m_3337_: *mut LeanObject,
    mut v_a_3338_: *mut LeanObject,
    mut v_b_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4___redArg(v_m_3337_, v_a_3338_, v_b_3339_);
    return v___x_3340_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3341_: *mut LeanObject,
    mut v_x_3342_: *mut LeanObject,
    mut v_x_3343_: usize,
    mut v_x_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    v___x_3345_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___redArg(v_x_3342_, v_x_3343_, v_x_3344_);
    return v___x_3345_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3346_: *mut LeanObject,
    mut v_x_3347_: *mut LeanObject,
    mut v_x_3348_: *mut LeanObject,
    mut v_x_3349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1782__boxed_3350_: usize = 0;
    let mut v_res_3351_: *mut LeanObject = core::ptr::null_mut();
    v_x_1782__boxed_3350_ = lean_unbox_usize(v_x_3348_);
    lean_dec(v_x_3348_);
    v_res_3351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1(v_00_u03b2_3346_, v_x_3347_, v_x_1782__boxed_3350_, v_x_3349_);
    lean_dec(v_x_3349_);
    lean_dec_ref(v_x_3347_);
    return v_res_3351_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
    mut v_x_3354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    v___x_3355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___redArg(v_a_3353_, v_x_3354_);
    return v___x_3355_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
    mut v_x_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3359_: *mut LeanObject = core::ptr::null_mut();
    v_res_3359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__1_spec__3(v_00_u03b2_3356_, v_a_3357_, v_x_3358_);
    lean_dec(v_x_3358_);
    lean_dec(v_a_3357_);
    return v_res_3359_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(
    mut v_00_u03b2_3360_: *mut LeanObject,
    mut v_x_3361_: *mut LeanObject,
    mut v_x_3362_: usize,
    mut v_x_3363_: usize,
    mut v_x_3364_: *mut LeanObject,
    mut v_x_3365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___redArg(v_x_3361_, v_x_3362_, v_x_3363_, v_x_3364_, v_x_3365_);
    return v___x_3366_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_3367_: *mut LeanObject,
    mut v_x_3368_: *mut LeanObject,
    mut v_x_3369_: *mut LeanObject,
    mut v_x_3370_: *mut LeanObject,
    mut v_x_3371_: *mut LeanObject,
    mut v_x_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1798__boxed_3373_: usize = 0;
    let mut v_x_1799__boxed_3374_: usize = 0;
    let mut v_res_3375_: *mut LeanObject = core::ptr::null_mut();
    v_x_1798__boxed_3373_ = lean_unbox_usize(v_x_3369_);
    lean_dec(v_x_3369_);
    v_x_1799__boxed_3374_ = lean_unbox_usize(v_x_3370_);
    lean_dec(v_x_3370_);
    v_res_3375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6(v_00_u03b2_3367_, v_x_3368_, v_x_1798__boxed_3373_, v_x_1799__boxed_3374_, v_x_3371_, v_x_3372_);
    return v_res_3375_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(
    mut v_00_u03b2_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_x_3378_: *mut LeanObject,
) -> u8 {
    let mut v___x_3379_: u8 = 0;
    v___x_3379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___redArg(v_a_3377_, v_x_3378_);
    return v___x_3379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8___boxed(
    mut v_00_u03b2_3380_: *mut LeanObject,
    mut v_a_3381_: *mut LeanObject,
    mut v_x_3382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3383_: u8 = 0;
    let mut v_r_3384_: *mut LeanObject = core::ptr::null_mut();
    v_res_3383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__8(v_00_u03b2_3380_, v_a_3381_, v_x_3382_);
    lean_dec(v_x_3382_);
    lean_dec(v_a_3381_);
    v_r_3384_ = lean_box((v_res_3383_) as usize);
    return v_r_3384_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9(
    mut v_00_u03b2_3385_: *mut LeanObject,
    mut v_data_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    v___x_3387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9___redArg(v_data_3386_);
    return v___x_3387_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10(
    mut v_00_u03b2_3388_: *mut LeanObject,
    mut v_a_3389_: *mut LeanObject,
    mut v_b_3390_: *mut LeanObject,
    mut v_x_3391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    v___x_3392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__10___redArg(v_a_3389_, v_b_3390_, v_x_3391_);
    return v___x_3392_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3393_: *mut LeanObject,
    mut v_keys_3394_: *mut LeanObject,
    mut v_vals_3395_: *mut LeanObject,
    mut v_heq_3396_: *mut LeanObject,
    mut v_i_3397_: *mut LeanObject,
    mut v_k_3398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3394_, v_vals_3395_, v_i_3397_, v_k_3398_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3400_: *mut LeanObject,
    mut v_keys_3401_: *mut LeanObject,
    mut v_vals_3402_: *mut LeanObject,
    mut v_heq_3403_: *mut LeanObject,
    mut v_i_3404_: *mut LeanObject,
    mut v_k_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3406_: *mut LeanObject = core::ptr::null_mut();
    v_res_3406_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3400_, v_keys_3401_, v_vals_3402_, v_heq_3403_, v_i_3404_, v_k_3405_);
    lean_dec(v_k_3405_);
    lean_dec_ref(v_vals_3402_);
    lean_dec_ref(v_keys_3401_);
    return v_res_3406_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8(
    mut v_00_u03b2_3407_: *mut LeanObject,
    mut v_n_3408_: *mut LeanObject,
    mut v_k_3409_: *mut LeanObject,
    mut v_v_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8___redArg(v_n_3408_, v_k_3409_, v_v_3410_);
    return v___x_3411_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(
    mut v_00_u03b2_3412_: *mut LeanObject,
    mut v_depth_3413_: usize,
    mut v_keys_3414_: *mut LeanObject,
    mut v_vals_3415_: *mut LeanObject,
    mut v_heq_3416_: *mut LeanObject,
    mut v_i_3417_: *mut LeanObject,
    mut v_entries_3418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    v___x_3419_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___redArg(v_depth_3413_, v_keys_3414_, v_vals_3415_, v_i_3417_, v_entries_3418_);
    return v___x_3419_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9___boxed(
    mut v_00_u03b2_3420_: *mut LeanObject,
    mut v_depth_3421_: *mut LeanObject,
    mut v_keys_3422_: *mut LeanObject,
    mut v_vals_3423_: *mut LeanObject,
    mut v_heq_3424_: *mut LeanObject,
    mut v_i_3425_: *mut LeanObject,
    mut v_entries_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3427_: usize = 0;
    let mut v_res_3428_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3427_ = lean_unbox_usize(v_depth_3421_);
    lean_dec(v_depth_3421_);
    v_res_3428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__9(v_00_u03b2_3420_, v_depth_boxed_3427_, v_keys_3422_, v_vals_3423_, v_heq_3424_, v_i_3425_, v_entries_3426_);
    lean_dec_ref(v_vals_3423_);
    lean_dec_ref(v_keys_3422_);
    return v_res_3428_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13(
    mut v_00_u03b2_3429_: *mut LeanObject,
    mut v_i_3430_: *mut LeanObject,
    mut v_source_3431_: *mut LeanObject,
    mut v_target_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    v___x_3433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13___redArg(v_i_3430_, v_source_3431_, v_target_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10(
    mut v_00_u03b2_3434_: *mut LeanObject,
    mut v_x_3435_: *mut LeanObject,
    mut v_x_3436_: *mut LeanObject,
    mut v_x_3437_: *mut LeanObject,
    mut v_x_3438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    v___x_3439_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__3_spec__6_spec__8_spec__10___redArg(v_x_3435_, v_x_3436_, v_x_3437_, v_x_3438_);
    return v___x_3439_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15(
    mut v_00_u03b2_3440_: *mut LeanObject,
    mut v_x_3441_: *mut LeanObject,
    mut v_x_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    v___x_3443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__1_spec__4_spec__9_spec__13_spec__15___redArg(v_x_3441_, v_x_3442_);
    return v___x_3443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(
    mut v_descr_3444_: *mut LeanObject,
    mut v_as_3445_: *mut LeanObject,
    mut v_sz_3446_: usize,
    mut v_i_3447_: usize,
    mut v_b_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: usize = 0;
    let mut v___x_3454_: usize = 0;
    let mut v___x_3456_: u8 = 0;
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_a_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofOLeanEntry_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addEntry_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut v_a_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofOLeanEntry_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3456_ = lean_usize_dec_lt(v_i_3447_, v_sz_3446_);
                if v___x_3456_ == 0 {
                    lean_dec_ref(v_descr_3444_);
                    v___x_3457_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3457_, 0, v_b_3448_);
                    return v___x_3457_;
                } else {
                    v_fst_3458_ = lean_ctor_get(v_b_3448_, 0);
                    v_snd_3459_ = lean_ctor_get(v_b_3448_, 1);
                    v_isSharedCheck_3498_ = (!lean_is_exclusive(v_b_3448_)) as u8;
                    if v_isSharedCheck_3498_ == 0 {
                        v___x_3461_ = v_b_3448_;
                        v_isShared_3462_ = v_isSharedCheck_3498_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3459_);
                        lean_inc(v_fst_3458_);
                        lean_dec(v_b_3448_);
                        v___x_3461_ = lean_box(0);
                        v_isShared_3462_ = v_isSharedCheck_3498_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3453_ = 1usize;
                v___x_3454_ = lean_usize_add(v_i_3447_, v___x_3453_);
                v_i_3447_ = v___x_3454_;
                v_b_3448_ = v_a_3452_;
                state = 0;
                continue;
            }
            2 => {
                v_a_3463_ = lean_array_uget_borrowed(v_as_3445_, v_i_3447_);
                if lean_obj_tag(v_a_3463_) == 0 {
                    v_a_3464_ = lean_ctor_get(v_a_3463_, 0);
                    v_ofOLeanEntry_3465_ = lean_ctor_get(v_descr_3444_, 2);
                    v_addEntry_3466_ = lean_ctor_get(v_descr_3444_, 4);
                    lean_inc_ref(v_ofOLeanEntry_3465_);
                    lean_inc_ref(v___y_3449_);
                    lean_inc(v_a_3464_);
                    lean_inc(v_fst_3458_);
                    v___x_3467_ = lean_apply_4(
                        v_ofOLeanEntry_3465_,
                        v_fst_3458_,
                        v_a_3464_,
                        v___y_3449_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3467_) == 0 {
                        v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
                        lean_inc(v_a_3468_);
                        lean_dec_ref_known(v___x_3467_, 1);
                        lean_inc(v_addEntry_3466_);
                        v___x_3469_ = lean_apply_2(v_addEntry_3466_, v_fst_3458_, v_a_3468_);
                        if v_isShared_3462_ == 0 {
                            lean_ctor_set(v___x_3461_, 0, v___x_3469_);
                            v___x_3471_ = v___x_3461_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
                            lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_snd_3459_);
                            v___x_3471_ = v_reuseFailAlloc_3472_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3461_);
                        lean_dec(v_snd_3459_);
                        lean_dec(v_fst_3458_);
                        lean_dec_ref(v_descr_3444_);
                        v_a_3473_ = lean_ctor_get(v___x_3467_, 0);
                        v_isSharedCheck_3480_ = (!lean_is_exclusive(v___x_3467_)) as u8;
                        if v_isSharedCheck_3480_ == 0 {
                            v___x_3475_ = v___x_3467_;
                            v_isShared_3476_ = v_isSharedCheck_3480_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3473_);
                            lean_dec(v___x_3467_);
                            v___x_3475_ = lean_box(0);
                            v_isShared_3476_ = v_isSharedCheck_3480_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_3481_ = lean_ctor_get(v_a_3463_, 0);
                    v_a_3482_ = lean_ctor_get(v_a_3463_, 1);
                    v_ofOLeanEntry_3483_ = lean_ctor_get(v_descr_3444_, 2);
                    lean_inc_ref(v_ofOLeanEntry_3483_);
                    lean_inc_ref(v___y_3449_);
                    lean_inc(v_a_3482_);
                    lean_inc(v_fst_3458_);
                    v___x_3484_ = lean_apply_4(
                        v_ofOLeanEntry_3483_,
                        v_fst_3458_,
                        v_a_3482_,
                        v___y_3449_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3484_) == 0 {
                        v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
                        lean_inc(v_a_3485_);
                        lean_dec_ref_known(v___x_3484_, 1);
                        lean_inc(v_a_3481_);
                        v___x_3486_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
                            v_snd_3459_,
                            v_a_3481_,
                            v_a_3485_,
                        );
                        if v_isShared_3462_ == 0 {
                            lean_ctor_set(v___x_3461_, 1, v___x_3486_);
                            v___x_3488_ = v___x_3461_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_fst_3458_);
                            lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3486_);
                            v___x_3488_ = v_reuseFailAlloc_3489_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3461_);
                        lean_dec(v_snd_3459_);
                        lean_dec(v_fst_3458_);
                        lean_dec_ref(v_descr_3444_);
                        v_a_3490_ = lean_ctor_get(v___x_3484_, 0);
                        v_isSharedCheck_3497_ = (!lean_is_exclusive(v___x_3484_)) as u8;
                        if v_isSharedCheck_3497_ == 0 {
                            v___x_3492_ = v___x_3484_;
                            v_isShared_3493_ = v_isSharedCheck_3497_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3490_);
                            lean_dec(v___x_3484_);
                            v___x_3492_ = lean_box(0);
                            v_isShared_3493_ = v_isSharedCheck_3497_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_3452_ = v___x_3471_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_3476_ == 0 {
                    v___x_3478_ = v___x_3475_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
                    v___x_3478_ = v_reuseFailAlloc_3479_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3478_;
            }
            6 => {
                v_a_3452_ = v___x_3488_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3493_ == 0 {
                    v___x_3495_ = v___x_3492_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
                    v___x_3495_ = v_reuseFailAlloc_3496_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg___boxed(
    mut v_descr_3499_: *mut LeanObject,
    mut v_as_3500_: *mut LeanObject,
    mut v_sz_3501_: *mut LeanObject,
    mut v_i_3502_: *mut LeanObject,
    mut v_b_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
    mut v___y_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3506_: usize = 0;
    let mut v_i_boxed_3507_: usize = 0;
    let mut v_res_3508_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3506_ = lean_unbox_usize(v_sz_3501_);
    lean_dec(v_sz_3501_);
    v_i_boxed_3507_ = lean_unbox_usize(v_i_3502_);
    lean_dec(v_i_3502_);
    v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_3499_, v_as_3500_, v_sz_boxed_3506_, v_i_boxed_3507_, v_b_3503_, v___y_3504_);
    lean_dec_ref(v___y_3504_);
    lean_dec_ref(v_as_3500_);
    return v_res_3508_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(
    mut v_descr_3509_: *mut LeanObject,
    mut v_as_3510_: *mut LeanObject,
    mut v_sz_3511_: usize,
    mut v_i_3512_: usize,
    mut v_b_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v_a_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3526_: usize = 0;
    let mut v___x_3527_: usize = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3534_: u8 = 0;
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: usize = 0;
    let mut v_reuseFailAlloc_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut v_reuseFailAlloc_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3516_ = lean_usize_dec_lt(v_i_3512_, v_sz_3511_);
                if v___x_3516_ == 0 {
                    lean_dec_ref(v_descr_3509_);
                    v___x_3517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3517_, 0, v_b_3513_);
                    return v___x_3517_;
                } else {
                    v_fst_3518_ = lean_ctor_get(v_b_3513_, 0);
                    v_snd_3519_ = lean_ctor_get(v_b_3513_, 1);
                    v_isSharedCheck_3543_ = (!lean_is_exclusive(v_b_3513_)) as u8;
                    if v_isSharedCheck_3543_ == 0 {
                        v___x_3521_ = v_b_3513_;
                        v_isShared_3522_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3519_);
                        lean_inc(v_fst_3518_);
                        lean_dec(v_b_3513_);
                        v___x_3521_ = lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3543_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3523_ = lean_array_uget_borrowed(v_as_3510_, v_i_3512_);
                if v_isShared_3522_ == 0 {
                    v___x_3525_ = v___x_3521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_fst_3518_);
                    lean_ctor_set(v_reuseFailAlloc_3542_, 1, v_snd_3519_);
                    v___x_3525_ = v_reuseFailAlloc_3542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_3526_ = lean_array_size(v_a_3523_);
                v___x_3527_ = 0usize;
                lean_inc_ref(v_descr_3509_);
                v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_3509_, v_a_3523_, v_sz_3526_, v___x_3527_, v___x_3525_, v___y_3514_);
                if lean_obj_tag(v___x_3528_) == 0 {
                    v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
                    lean_inc(v_a_3529_);
                    lean_dec_ref_known(v___x_3528_, 1);
                    v_fst_3530_ = lean_ctor_get(v_a_3529_, 0);
                    v_snd_3531_ = lean_ctor_get(v_a_3529_, 1);
                    v_isSharedCheck_3541_ = (!lean_is_exclusive(v_a_3529_)) as u8;
                    if v_isSharedCheck_3541_ == 0 {
                        v___x_3533_ = v_a_3529_;
                        v_isShared_3534_ = v_isSharedCheck_3541_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_3531_);
                        lean_inc(v_fst_3530_);
                        lean_dec(v_a_3529_);
                        v___x_3533_ = lean_box(0);
                        v_isShared_3534_ = v_isSharedCheck_3541_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_descr_3509_);
                    return v___x_3528_;
                }
            }
            3 => {
                if v_isShared_3534_ == 0 {
                    v___x_3536_ = v___x_3533_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_fst_3530_);
                    lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_snd_3531_);
                    v___x_3536_ = v_reuseFailAlloc_3540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3537_ = 1usize;
                v___x_3538_ = lean_usize_add(v_i_3512_, v___x_3537_);
                v_i_3512_ = v___x_3538_;
                v_b_3513_ = v___x_3536_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg___boxed(
    mut v_descr_3544_: *mut LeanObject,
    mut v_as_3545_: *mut LeanObject,
    mut v_sz_3546_: *mut LeanObject,
    mut v_i_3547_: *mut LeanObject,
    mut v_b_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3551_: usize = 0;
    let mut v_i_boxed_3552_: usize = 0;
    let mut v_res_3553_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3551_ = lean_unbox_usize(v_sz_3546_);
    lean_dec(v_sz_3546_);
    v_i_boxed_3552_ = lean_unbox_usize(v_i_3547_);
    lean_dec(v_i_3547_);
    v_res_3553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_3544_, v_as_3545_, v_sz_boxed_3551_, v_i_boxed_3552_, v_b_3548_, v___y_3549_);
    lean_dec_ref(v___y_3549_);
    lean_dec_ref(v_as_3545_);
    return v_res_3553_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn___redArg(
    mut v_descr_3554_: *mut LeanObject,
    mut v_as_3555_: *mut LeanObject,
    mut v_a_3556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mkInitial_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finalizeImport_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3565_: usize = 0;
    let mut v___x_3566_: usize = 0;
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v_fst_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_a_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3593_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3597_: u8 = 0;
    let mut v_a_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mkInitial_3558_ = lean_ctor_get(v_descr_3554_, 1);
                v_finalizeImport_3559_ = lean_ctor_get(v_descr_3554_, 5);
                lean_inc(v_finalizeImport_3559_);
                lean_inc_ref(v_mkInitial_3558_);
                v___x_3560_ = lean_apply_1(v_mkInitial_3558_, lean_box(0));
                if lean_obj_tag(v___x_3560_) == 0 {
                    v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
                    lean_inc(v_a_3561_);
                    lean_dec_ref_known(v___x_3560_, 1);
                    v___x_3562_ = 1;
                    v___x_3563_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4_once), _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries_default___closed__4);
                    v___x_3564_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3564_, 0, v_a_3561_);
                    lean_ctor_set(v___x_3564_, 1, v___x_3563_);
                    v_sz_3565_ = lean_array_size(v_as_3555_);
                    v___x_3566_ = 0usize;
                    v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_3554_, v_as_3555_, v_sz_3565_, v___x_3566_, v___x_3564_, v_a_3556_);
                    if lean_obj_tag(v___x_3567_) == 0 {
                        v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
                        v_isSharedCheck_3589_ = (!lean_is_exclusive(v___x_3567_)) as u8;
                        if v_isSharedCheck_3589_ == 0 {
                            v___x_3570_ = v___x_3567_;
                            v_isShared_3571_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3568_);
                            lean_dec(v___x_3567_);
                            v___x_3570_ = lean_box(0);
                            v_isShared_3571_ = v_isSharedCheck_3589_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_finalizeImport_3559_);
                        v_a_3590_ = lean_ctor_get(v___x_3567_, 0);
                        v_isSharedCheck_3597_ = (!lean_is_exclusive(v___x_3567_)) as u8;
                        if v_isSharedCheck_3597_ == 0 {
                            v___x_3592_ = v___x_3567_;
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3590_);
                            lean_dec(v___x_3567_);
                            v___x_3592_ = lean_box(0);
                            v_isShared_3593_ = v_isSharedCheck_3597_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_finalizeImport_3559_);
                    lean_dec_ref(v_descr_3554_);
                    v_a_3598_ = lean_ctor_get(v___x_3560_, 0);
                    v_isSharedCheck_3605_ = (!lean_is_exclusive(v___x_3560_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v___x_3600_ = v___x_3560_;
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3598_);
                        lean_dec(v___x_3560_);
                        v___x_3600_ = lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3605_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3572_ = lean_ctor_get(v_a_3568_, 0);
                v_snd_3573_ = lean_ctor_get(v_a_3568_, 1);
                v_isSharedCheck_3588_ = (!lean_is_exclusive(v_a_3568_)) as u8;
                if v_isSharedCheck_3588_ == 0 {
                    v___x_3575_ = v_a_3568_;
                    v_isShared_3576_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3573_);
                    lean_inc(v_fst_3572_);
                    lean_dec(v_a_3568_);
                    v___x_3575_ = lean_box(0);
                    v_isShared_3576_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3577_ = lean_apply_1(v_finalizeImport_3559_, v_fst_3572_);
                v___x_3578_ = l_Lean_NameSet_empty;
                v___x_3579_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3579_, 0, v___x_3577_);
                lean_ctor_set(v___x_3579_, 1, v___x_3578_);
                lean_ctor_set_uint8(
                    v___x_3579_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3562_,
                );
                v___x_3580_ = lean_box(0);
                if v_isShared_3576_ == 0 {
                    lean_ctor_set_tag(v___x_3575_, 1);
                    lean_ctor_set(v___x_3575_, 1, v___x_3580_);
                    lean_ctor_set(v___x_3575_, 0, v___x_3579_);
                    v___x_3582_ = v___x_3575_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3579_);
                    lean_ctor_set(v_reuseFailAlloc_3587_, 1, v___x_3580_);
                    v___x_3582_ = v_reuseFailAlloc_3587_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3583_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3583_, 0, v___x_3582_);
                lean_ctor_set(v___x_3583_, 1, v_snd_3573_);
                lean_ctor_set(v___x_3583_, 2, v___x_3580_);
                if v_isShared_3571_ == 0 {
                    lean_ctor_set(v___x_3570_, 0, v___x_3583_);
                    v___x_3585_ = v___x_3570_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
                    v___x_3585_ = v_reuseFailAlloc_3586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3585_;
            }
            5 => {
                if v_isShared_3593_ == 0 {
                    v___x_3595_ = v___x_3592_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
                    v___x_3595_ = v_reuseFailAlloc_3596_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3595_;
            }
            7 => {
                if v_isShared_3601_ == 0 {
                    v___x_3603_ = v___x_3600_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn___redArg___boxed(
    mut v_descr_3606_: *mut LeanObject,
    mut v_as_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3610_: *mut LeanObject = core::ptr::null_mut();
    v_res_3610_ =
        l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_3606_, v_as_3607_, v_a_3608_);
    lean_dec_ref(v_a_3608_);
    lean_dec_ref(v_as_3607_);
    return v_res_3610_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn(
    mut v_00_u03b1_3611_: *mut LeanObject,
    mut v_00_u03b2_3612_: *mut LeanObject,
    mut v_00_u03c3_3613_: *mut LeanObject,
    mut v_descr_3614_: *mut LeanObject,
    mut v_as_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    v___x_3618_ =
        l_Lean_ScopedEnvExtension_addImportedFn___redArg(v_descr_3614_, v_as_3615_, v_a_3616_);
    return v___x_3618_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addImportedFn___boxed(
    mut v_00_u03b1_3619_: *mut LeanObject,
    mut v_00_u03b2_3620_: *mut LeanObject,
    mut v_00_u03c3_3621_: *mut LeanObject,
    mut v_descr_3622_: *mut LeanObject,
    mut v_as_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
    mut v_a_3625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3626_: *mut LeanObject = core::ptr::null_mut();
    v_res_3626_ = l_Lean_ScopedEnvExtension_addImportedFn(
        v_00_u03b1_3619_,
        v_00_u03b2_3620_,
        v_00_u03c3_3621_,
        v_descr_3622_,
        v_as_3623_,
        v_a_3624_,
    );
    lean_dec_ref(v_a_3624_);
    lean_dec_ref(v_as_3623_);
    return v_res_3626_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(
    mut v_00_u03b1_3627_: *mut LeanObject,
    mut v_00_u03c3_3628_: *mut LeanObject,
    mut v_00_u03b2_3629_: *mut LeanObject,
    mut v_descr_3630_: *mut LeanObject,
    mut v_as_3631_: *mut LeanObject,
    mut v_sz_3632_: usize,
    mut v_i_3633_: usize,
    mut v_b_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    v___x_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___redArg(v_descr_3630_, v_as_3631_, v_sz_3632_, v_i_3633_, v_b_3634_, v___y_3635_);
    return v___x_3637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0___boxed(
    mut v_00_u03b1_3638_: *mut LeanObject,
    mut v_00_u03c3_3639_: *mut LeanObject,
    mut v_00_u03b2_3640_: *mut LeanObject,
    mut v_descr_3641_: *mut LeanObject,
    mut v_as_3642_: *mut LeanObject,
    mut v_sz_3643_: *mut LeanObject,
    mut v_i_3644_: *mut LeanObject,
    mut v_b_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3648_: usize = 0;
    let mut v_i_boxed_3649_: usize = 0;
    let mut v_res_3650_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3648_ = lean_unbox_usize(v_sz_3643_);
    lean_dec(v_sz_3643_);
    v_i_boxed_3649_ = lean_unbox_usize(v_i_3644_);
    lean_dec(v_i_3644_);
    v_res_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__0(v_00_u03b1_3638_, v_00_u03c3_3639_, v_00_u03b2_3640_, v_descr_3641_, v_as_3642_, v_sz_boxed_3648_, v_i_boxed_3649_, v_b_3645_, v___y_3646_);
    lean_dec_ref(v___y_3646_);
    lean_dec_ref(v_as_3642_);
    return v_res_3650_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(
    mut v_00_u03b1_3651_: *mut LeanObject,
    mut v_00_u03c3_3652_: *mut LeanObject,
    mut v_00_u03b2_3653_: *mut LeanObject,
    mut v_descr_3654_: *mut LeanObject,
    mut v_as_3655_: *mut LeanObject,
    mut v_sz_3656_: usize,
    mut v_i_3657_: usize,
    mut v_b_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___redArg(v_descr_3654_, v_as_3655_, v_sz_3656_, v_i_3657_, v_b_3658_, v___y_3659_);
    return v___x_3661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1___boxed(
    mut v_00_u03b1_3662_: *mut LeanObject,
    mut v_00_u03c3_3663_: *mut LeanObject,
    mut v_00_u03b2_3664_: *mut LeanObject,
    mut v_descr_3665_: *mut LeanObject,
    mut v_as_3666_: *mut LeanObject,
    mut v_sz_3667_: *mut LeanObject,
    mut v_i_3668_: *mut LeanObject,
    mut v_b_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
    mut v___y_3671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3672_: usize = 0;
    let mut v_i_boxed_3673_: usize = 0;
    let mut v_res_3674_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3672_ = lean_unbox_usize(v_sz_3667_);
    lean_dec(v_sz_3667_);
    v_i_boxed_3673_ = lean_unbox_usize(v_i_3668_);
    lean_dec(v_i_3668_);
    v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_addImportedFn_spec__1(v_00_u03b1_3662_, v_00_u03c3_3663_, v_00_u03b2_3664_, v_descr_3665_, v_as_3666_, v_sz_boxed_3672_, v_i_boxed_3673_, v_b_3669_, v___y_3670_);
    lean_dec_ref(v___y_3670_);
    lean_dec_ref(v_as_3666_);
    return v_res_3674_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
    mut v_a_3675_: *mut LeanObject,
    mut v_descr_3676_: *mut LeanObject,
    mut v_a_3677_: *mut LeanObject,
    mut v_a_3678_: *mut LeanObject,
    mut v_a_3679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3685_: u8 = 0;
    let mut v___y_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_3694_: u8 = 0;
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v_addEntry_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3704_: u8 = 0;
    let mut v_unused_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3678_) == 0 {
                    lean_dec(v_a_3677_);
                    lean_dec_ref(v_descr_3676_);
                    v___x_3680_ = l_List_reverse___redArg(v_a_3679_);
                    return v___x_3680_;
                } else {
                    v_head_3681_ = lean_ctor_get(v_a_3678_, 0);
                    v_tail_3682_ = lean_ctor_get(v_a_3678_, 1);
                    v_isSharedCheck_3707_ = (!lean_is_exclusive(v_a_3678_)) as u8;
                    if v_isSharedCheck_3707_ == 0 {
                        v___x_3684_ = v_a_3678_;
                        v_isShared_3685_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3682_);
                        lean_inc(v_head_3681_);
                        lean_dec(v_a_3678_);
                        v___x_3684_ = lean_box(0);
                        v_isShared_3685_ = v_isSharedCheck_3707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_state_3692_ = lean_ctor_get(v_head_3681_, 0);
                v_activeScopes_3693_ = lean_ctor_get(v_head_3681_, 1);
                v_delimitsLocal_3694_ = lean_ctor_get_uint8(
                    v_head_3681_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v___x_3695_ = l_Lean_NameSet_contains(v_activeScopes_3693_, v_a_3675_);
                if v___x_3695_ == 0 {
                    v___y_3687_ = v_head_3681_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_activeScopes_3693_);
                    lean_inc(v_state_3692_);
                    v_isSharedCheck_3704_ = (!lean_is_exclusive(v_head_3681_)) as u8;
                    if v_isSharedCheck_3704_ == 0 {
                        v_unused_3705_ = lean_ctor_get(v_head_3681_, 1);
                        lean_dec(v_unused_3705_);
                        v_unused_3706_ = lean_ctor_get(v_head_3681_, 0);
                        lean_dec(v_unused_3706_);
                        v___x_3697_ = v_head_3681_;
                        v_isShared_3698_ = v_isSharedCheck_3704_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_head_3681_);
                        v___x_3697_ = lean_box(0);
                        v_isShared_3698_ = v_isSharedCheck_3704_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3685_ == 0 {
                    lean_ctor_set(v___x_3684_, 1, v_a_3679_);
                    lean_ctor_set(v___x_3684_, 0, v___y_3687_);
                    v___x_3689_ = v___x_3684_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___y_3687_);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_a_3679_);
                    v___x_3689_ = v_reuseFailAlloc_3691_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_3678_ = v_tail_3682_;
                v_a_3679_ = v___x_3689_;
                state = 0;
                continue;
            }
            4 => {
                v_addEntry_3699_ = lean_ctor_get(v_descr_3676_, 4);
                lean_inc(v_addEntry_3699_);
                lean_inc(v_a_3677_);
                v___x_3700_ = lean_apply_2(v_addEntry_3699_, v_state_3692_, v_a_3677_);
                if v_isShared_3698_ == 0 {
                    lean_ctor_set(v___x_3697_, 0, v___x_3700_);
                    v___x_3702_ = v___x_3697_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
                    lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_activeScopes_3693_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3703_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_delimitsLocal_3694_,
                    );
                    v___x_3702_ = v_reuseFailAlloc_3703_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3687_ = v___x_3702_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg___boxed(
    mut v_a_3708_: *mut LeanObject,
    mut v_descr_3709_: *mut LeanObject,
    mut v_a_3710_: *mut LeanObject,
    mut v_a_3711_: *mut LeanObject,
    mut v_a_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3713_: *mut LeanObject = core::ptr::null_mut();
    v_res_3713_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
        v_a_3708_,
        v_descr_3709_,
        v_a_3710_,
        v_a_3711_,
        v_a_3712_,
    );
    lean_dec(v_a_3708_);
    return v_res_3713_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(
    mut v_descr_3714_: *mut LeanObject,
    mut v_a_3715_: *mut LeanObject,
    mut v_a_3716_: *mut LeanObject,
    mut v_a_3717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v_addEntry_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_3727_: u8 = 0;
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut v_isSharedCheck_3740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3716_) == 0 {
                    lean_dec(v_a_3715_);
                    lean_dec_ref(v_descr_3714_);
                    v___x_3718_ = l_List_reverse___redArg(v_a_3717_);
                    return v___x_3718_;
                } else {
                    v_head_3719_ = lean_ctor_get(v_a_3716_, 0);
                    v_tail_3720_ = lean_ctor_get(v_a_3716_, 1);
                    v_isSharedCheck_3740_ = (!lean_is_exclusive(v_a_3716_)) as u8;
                    if v_isSharedCheck_3740_ == 0 {
                        v___x_3722_ = v_a_3716_;
                        v_isShared_3723_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3720_);
                        lean_inc(v_head_3719_);
                        lean_dec(v_a_3716_);
                        v___x_3722_ = lean_box(0);
                        v_isShared_3723_ = v_isSharedCheck_3740_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_3724_ = lean_ctor_get(v_descr_3714_, 4);
                v_state_3725_ = lean_ctor_get(v_head_3719_, 0);
                v_activeScopes_3726_ = lean_ctor_get(v_head_3719_, 1);
                v_delimitsLocal_3727_ = lean_ctor_get_uint8(
                    v_head_3719_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_3739_ = (!lean_is_exclusive(v_head_3719_)) as u8;
                if v_isSharedCheck_3739_ == 0 {
                    v___x_3729_ = v_head_3719_;
                    v_isShared_3730_ = v_isSharedCheck_3739_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_activeScopes_3726_);
                    lean_inc(v_state_3725_);
                    lean_dec(v_head_3719_);
                    v___x_3729_ = lean_box(0);
                    v_isShared_3730_ = v_isSharedCheck_3739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_addEntry_3724_);
                lean_inc(v_a_3715_);
                v___x_3731_ = lean_apply_2(v_addEntry_3724_, v_state_3725_, v_a_3715_);
                if v_isShared_3730_ == 0 {
                    lean_ctor_set(v___x_3729_, 0, v___x_3731_);
                    v___x_3733_ = v___x_3729_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3731_);
                    lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_activeScopes_3726_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3738_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_delimitsLocal_3727_,
                    );
                    v___x_3733_ = v_reuseFailAlloc_3738_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3723_ == 0 {
                    lean_ctor_set(v___x_3722_, 1, v_a_3717_);
                    lean_ctor_set(v___x_3722_, 0, v___x_3733_);
                    v___x_3735_ = v___x_3722_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3733_);
                    lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_a_3717_);
                    v___x_3735_ = v_reuseFailAlloc_3737_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3716_ = v_tail_3720_;
                v_a_3717_ = v___x_3735_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntryFn___redArg(
    mut v_descr_3741_: *mut LeanObject,
    mut v_s_3742_: *mut LeanObject,
    mut v_e_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stateStack_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v_a_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3753_: u8 = 0;
    let mut v_toOLeanEntry_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_stateStack_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v_a_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3777_: u8 = 0;
    let mut v_toOLeanEntry_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3743_) == 0 {
                    v_stateStack_3744_ = lean_ctor_get(v_s_3742_, 0);
                    v_scopedEntries_3745_ = lean_ctor_get(v_s_3742_, 1);
                    v_newEntries_3746_ = lean_ctor_get(v_s_3742_, 2);
                    v_isSharedCheck_3766_ = (!lean_is_exclusive(v_s_3742_)) as u8;
                    if v_isSharedCheck_3766_ == 0 {
                        v___x_3748_ = v_s_3742_;
                        v_isShared_3749_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_newEntries_3746_);
                        lean_inc(v_scopedEntries_3745_);
                        lean_inc(v_stateStack_3744_);
                        lean_dec(v_s_3742_);
                        v___x_3748_ = lean_box(0);
                        v_isShared_3749_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_stateStack_3767_ = lean_ctor_get(v_s_3742_, 0);
                    v_scopedEntries_3768_ = lean_ctor_get(v_s_3742_, 1);
                    v_newEntries_3769_ = lean_ctor_get(v_s_3742_, 2);
                    v_isSharedCheck_3791_ = (!lean_is_exclusive(v_s_3742_)) as u8;
                    if v_isSharedCheck_3791_ == 0 {
                        v___x_3771_ = v_s_3742_;
                        v_isShared_3772_ = v_isSharedCheck_3791_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_newEntries_3769_);
                        lean_inc(v_scopedEntries_3768_);
                        lean_inc(v_stateStack_3767_);
                        lean_dec(v_s_3742_);
                        v___x_3771_ = lean_box(0);
                        v_isShared_3772_ = v_isSharedCheck_3791_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3750_ = lean_ctor_get(v_e_3743_, 0);
                v_isSharedCheck_3765_ = (!lean_is_exclusive(v_e_3743_)) as u8;
                if v_isSharedCheck_3765_ == 0 {
                    v___x_3752_ = v_e_3743_;
                    v_isShared_3753_ = v_isSharedCheck_3765_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_3750_);
                    lean_dec(v_e_3743_);
                    v___x_3752_ = lean_box(0);
                    v_isShared_3753_ = v_isSharedCheck_3765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toOLeanEntry_3754_ = lean_ctor_get(v_descr_3741_, 3);
                lean_inc(v_toOLeanEntry_3754_);
                v___x_3755_ = lean_box(0);
                lean_inc(v_a_3750_);
                v___x_3756_ =
                    l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(
                        v_descr_3741_,
                        v_a_3750_,
                        v_stateStack_3744_,
                        v___x_3755_,
                    );
                v___x_3757_ = lean_apply_1(v_toOLeanEntry_3754_, v_a_3750_);
                if v_isShared_3753_ == 0 {
                    lean_ctor_set(v___x_3752_, 0, v___x_3757_);
                    v___x_3759_ = v___x_3752_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3757_);
                    v___x_3759_ = v_reuseFailAlloc_3764_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3760_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3760_, 0, v___x_3759_);
                lean_ctor_set(v___x_3760_, 1, v_newEntries_3746_);
                if v_isShared_3749_ == 0 {
                    lean_ctor_set(v___x_3748_, 2, v___x_3760_);
                    lean_ctor_set(v___x_3748_, 0, v___x_3756_);
                    v___x_3762_ = v___x_3748_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3756_);
                    lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_scopedEntries_3745_);
                    lean_ctor_set(v_reuseFailAlloc_3763_, 2, v___x_3760_);
                    v___x_3762_ = v_reuseFailAlloc_3763_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3762_;
            }
            5 => {
                v_a_3773_ = lean_ctor_get(v_e_3743_, 0);
                v_a_3774_ = lean_ctor_get(v_e_3743_, 1);
                v_isSharedCheck_3790_ = (!lean_is_exclusive(v_e_3743_)) as u8;
                if v_isSharedCheck_3790_ == 0 {
                    v___x_3776_ = v_e_3743_;
                    v_isShared_3777_ = v_isSharedCheck_3790_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_a_3774_);
                    lean_inc(v_a_3773_);
                    lean_dec(v_e_3743_);
                    v___x_3776_ = lean_box(0);
                    v_isShared_3777_ = v_isSharedCheck_3790_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_toOLeanEntry_3778_ = lean_ctor_get(v_descr_3741_, 3);
                lean_inc(v_toOLeanEntry_3778_);
                v___x_3779_ = lean_box(0);
                lean_inc_n(v_a_3774_, 2);
                v___x_3780_ =
                    l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
                        v_a_3773_,
                        v_descr_3741_,
                        v_a_3774_,
                        v_stateStack_3767_,
                        v___x_3779_,
                    );
                lean_inc(v_a_3773_);
                v___x_3781_ = l_Lean_ScopedEnvExtension_ScopedEntries_insert___redArg(
                    v_scopedEntries_3768_,
                    v_a_3773_,
                    v_a_3774_,
                );
                v___x_3782_ = lean_apply_1(v_toOLeanEntry_3778_, v_a_3774_);
                if v_isShared_3777_ == 0 {
                    lean_ctor_set(v___x_3776_, 1, v___x_3782_);
                    v___x_3784_ = v___x_3776_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3773_);
                    lean_ctor_set(v_reuseFailAlloc_3789_, 1, v___x_3782_);
                    v___x_3784_ = v_reuseFailAlloc_3789_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3785_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3785_, 0, v___x_3784_);
                lean_ctor_set(v___x_3785_, 1, v_newEntries_3769_);
                if v_isShared_3772_ == 0 {
                    lean_ctor_set(v___x_3771_, 2, v___x_3785_);
                    lean_ctor_set(v___x_3771_, 1, v___x_3781_);
                    lean_ctor_set(v___x_3771_, 0, v___x_3780_);
                    v___x_3787_ = v___x_3771_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3780_);
                    lean_ctor_set(v_reuseFailAlloc_3788_, 1, v___x_3781_);
                    lean_ctor_set(v_reuseFailAlloc_3788_, 2, v___x_3785_);
                    v___x_3787_ = v_reuseFailAlloc_3788_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntryFn(
    mut v_00_u03b1_3792_: *mut LeanObject,
    mut v_00_u03b2_3793_: *mut LeanObject,
    mut v_00_u03c3_3794_: *mut LeanObject,
    mut v_descr_3795_: *mut LeanObject,
    mut v_s_3796_: *mut LeanObject,
    mut v_e_3797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    v___x_3798_ =
        l_Lean_ScopedEnvExtension_addEntryFn___redArg(v_descr_3795_, v_s_3796_, v_e_3797_);
    return v___x_3798_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0(
    mut v_00_u03c3_3799_: *mut LeanObject,
    mut v_00_u03b2_3800_: *mut LeanObject,
    mut v_00_u03b1_3801_: *mut LeanObject,
    mut v_descr_3802_: *mut LeanObject,
    mut v_a_3803_: *mut LeanObject,
    mut v_a_3804_: *mut LeanObject,
    mut v_a_3805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    v___x_3806_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__0___redArg(
        v_descr_3802_,
        v_a_3803_,
        v_a_3804_,
        v_a_3805_,
    );
    return v___x_3806_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(
    mut v_00_u03c3_3807_: *mut LeanObject,
    mut v_a_3808_: *mut LeanObject,
    mut v_00_u03b2_3809_: *mut LeanObject,
    mut v_00_u03b1_3810_: *mut LeanObject,
    mut v_descr_3811_: *mut LeanObject,
    mut v_a_3812_: *mut LeanObject,
    mut v_a_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    v___x_3815_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___redArg(
        v_a_3808_,
        v_descr_3811_,
        v_a_3812_,
        v_a_3813_,
        v_a_3814_,
    );
    return v___x_3815_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1___boxed(
    mut v_00_u03c3_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_00_u03b2_3818_: *mut LeanObject,
    mut v_00_u03b1_3819_: *mut LeanObject,
    mut v_descr_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_a_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3824_: *mut LeanObject = core::ptr::null_mut();
    v_res_3824_ = l_List_mapTR_loop___at___00Lean_ScopedEnvExtension_addEntryFn_spec__1(
        v_00_u03c3_3816_,
        v_a_3817_,
        v_00_u03b2_3818_,
        v_00_u03b1_3819_,
        v_descr_3820_,
        v_a_3821_,
        v_a_3822_,
        v_a_3823_,
    );
    lean_dec(v_a_3817_);
    return v_res_3824_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(
    mut v_descr_3825_: *mut LeanObject,
    mut v_env_3826_: *mut LeanObject,
    mut v_as_3827_: *mut LeanObject,
    mut v_sz_3828_: usize,
    mut v_i_3829_: usize,
    mut v_b_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: usize = 0;
    let mut v___x_3834_: usize = 0;
    let mut v___x_3836_: u8 = 0;
    let mut v_snd_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v_fst_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v_a_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v_exportEntry_x3f_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_server_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_private_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_server_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_val_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_a_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v_exportEntry_x3f_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_server_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_private_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_server_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exported_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3836_ = lean_usize_dec_lt(v_i_3829_, v_sz_3828_);
                if v___x_3836_ == 0 {
                    lean_dec_ref(v_env_3826_);
                    lean_dec_ref(v_descr_3825_);
                    return v_b_3830_;
                } else {
                    v_snd_3837_ = lean_ctor_get(v_b_3830_, 1);
                    v_fst_3838_ = lean_ctor_get(v_b_3830_, 0);
                    v_isSharedCheck_3938_ = (!lean_is_exclusive(v_b_3830_)) as u8;
                    if v_isSharedCheck_3938_ == 0 {
                        v___x_3840_ = v_b_3830_;
                        v_isShared_3841_ = v_isSharedCheck_3938_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3837_);
                        lean_inc(v_fst_3838_);
                        lean_dec(v_b_3830_);
                        v___x_3840_ = lean_box(0);
                        v_isShared_3841_ = v_isSharedCheck_3938_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3833_ = 1usize;
                v___x_3834_ = lean_usize_add(v_i_3829_, v___x_3833_);
                v_i_3829_ = v___x_3834_;
                v_b_3830_ = v_a_3832_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3842_ = lean_ctor_get(v_snd_3837_, 0);
                v_snd_3843_ = lean_ctor_get(v_snd_3837_, 1);
                v_isSharedCheck_3937_ = (!lean_is_exclusive(v_snd_3837_)) as u8;
                if v_isSharedCheck_3937_ == 0 {
                    v___x_3845_ = v_snd_3837_;
                    v_isShared_3846_ = v_isSharedCheck_3937_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3843_);
                    lean_inc(v_fst_3842_);
                    lean_dec(v_snd_3837_);
                    v___x_3845_ = lean_box(0);
                    v_isShared_3846_ = v_isSharedCheck_3937_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_3847_ = lean_array_uget(v_as_3827_, v_i_3829_);
                if lean_obj_tag(v_a_3847_) == 0 {
                    v_a_3848_ = lean_ctor_get(v_a_3847_, 0);
                    v_isSharedCheck_3897_ = (!lean_is_exclusive(v_a_3847_)) as u8;
                    if v_isSharedCheck_3897_ == 0 {
                        v___x_3850_ = v_a_3847_;
                        v_isShared_3851_ = v_isSharedCheck_3897_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3848_);
                        lean_dec(v_a_3847_);
                        v___x_3850_ = lean_box(0);
                        v_isShared_3851_ = v_isSharedCheck_3897_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_3898_ = lean_ctor_get(v_a_3847_, 0);
                    v_a_3899_ = lean_ctor_get(v_a_3847_, 1);
                    v_isSharedCheck_3936_ = (!lean_is_exclusive(v_a_3847_)) as u8;
                    if v_isSharedCheck_3936_ == 0 {
                        v___x_3901_ = v_a_3847_;
                        v_isShared_3902_ = v_isSharedCheck_3936_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3899_);
                        lean_inc(v_a_3898_);
                        lean_dec(v_a_3847_);
                        v___x_3901_ = lean_box(0);
                        v_isShared_3902_ = v_isSharedCheck_3936_;
                        state = 16;
                        continue;
                    }
                }
            }
            4 => {
                v_exportEntry_x3f_3852_ = lean_ctor_get(v_descr_3825_, 6);
                lean_inc_ref(v_exportEntry_x3f_3852_);
                lean_inc_ref(v_env_3826_);
                v___x_3853_ = lean_apply_2(v_exportEntry_x3f_3852_, v_env_3826_, v_a_3848_);
                v_exported_3854_ = lean_ctor_get(v___x_3853_, 0);
                lean_inc(v_exported_3854_);
                v_server_3855_ = lean_ctor_get(v___x_3853_, 1);
                lean_inc(v_server_3855_);
                v_private_3856_ = lean_ctor_get(v___x_3853_, 2);
                lean_inc(v_private_3856_);
                lean_dec_ref(v___x_3853_);
                if lean_obj_tag(v_exported_3854_) == 1 {
                    v_val_3888_ = lean_ctor_get(v_exported_3854_, 0);
                    v_isSharedCheck_3896_ = (!lean_is_exclusive(v_exported_3854_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3890_ = v_exported_3854_;
                        v_isShared_3891_ = v_isSharedCheck_3896_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_val_3888_);
                        lean_dec(v_exported_3854_);
                        v___x_3890_ = lean_box(0);
                        v_isShared_3891_ = v_isSharedCheck_3896_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec(v_exported_3854_);
                    v_exported_3878_ = v_fst_3838_;
                    state = 11;
                    continue;
                }
            }
            5 => {
                if lean_obj_tag(v_private_3856_) == 1 {
                    v_val_3860_ = lean_ctor_get(v_private_3856_, 0);
                    lean_inc(v_val_3860_);
                    lean_dec_ref_known(v_private_3856_, 1);
                    if v_isShared_3851_ == 0 {
                        lean_ctor_set(v___x_3850_, 0, v_val_3860_);
                        v___x_3862_ = v___x_3850_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_val_3860_);
                        v___x_3862_ = v_reuseFailAlloc_3870_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_private_3856_);
                    lean_del_object(v___x_3850_);
                    if v_isShared_3846_ == 0 {
                        lean_ctor_set(v___x_3845_, 0, v_server_3859_);
                        v___x_3872_ = v___x_3845_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_server_3859_);
                        lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_snd_3843_);
                        v___x_3872_ = v_reuseFailAlloc_3876_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3863_ = lean_array_push(v_snd_3843_, v___x_3862_);
                if v_isShared_3846_ == 0 {
                    lean_ctor_set(v___x_3845_, 1, v___x_3863_);
                    lean_ctor_set(v___x_3845_, 0, v_server_3859_);
                    v___x_3865_ = v___x_3845_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_server_3859_);
                    lean_ctor_set(v_reuseFailAlloc_3869_, 1, v___x_3863_);
                    v___x_3865_ = v_reuseFailAlloc_3869_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3841_ == 0 {
                    lean_ctor_set(v___x_3840_, 1, v___x_3865_);
                    lean_ctor_set(v___x_3840_, 0, v___y_3858_);
                    v___x_3867_ = v___x_3840_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___y_3858_);
                    lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3865_);
                    v___x_3867_ = v_reuseFailAlloc_3868_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_3832_ = v___x_3867_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_3841_ == 0 {
                    lean_ctor_set(v___x_3840_, 1, v___x_3872_);
                    lean_ctor_set(v___x_3840_, 0, v___y_3858_);
                    v___x_3874_ = v___x_3840_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___y_3858_);
                    lean_ctor_set(v_reuseFailAlloc_3875_, 1, v___x_3872_);
                    v___x_3874_ = v_reuseFailAlloc_3875_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_3832_ = v___x_3874_;
                state = 1;
                continue;
            }
            11 => {
                if lean_obj_tag(v_server_3855_) == 1 {
                    v_val_3879_ = lean_ctor_get(v_server_3855_, 0);
                    v_isSharedCheck_3887_ = (!lean_is_exclusive(v_server_3855_)) as u8;
                    if v_isSharedCheck_3887_ == 0 {
                        v___x_3881_ = v_server_3855_;
                        v_isShared_3882_ = v_isSharedCheck_3887_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_val_3879_);
                        lean_dec(v_server_3855_);
                        v___x_3881_ = lean_box(0);
                        v_isShared_3882_ = v_isSharedCheck_3887_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v_server_3855_);
                    v___y_3858_ = v_exported_3878_;
                    v_server_3859_ = v_fst_3842_;
                    state = 5;
                    continue;
                }
            }
            12 => {
                if v_isShared_3882_ == 0 {
                    lean_ctor_set_tag(v___x_3881_, 0);
                    v___x_3884_ = v___x_3881_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_val_3879_);
                    v___x_3884_ = v_reuseFailAlloc_3886_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_3885_ = lean_array_push(v_fst_3842_, v___x_3884_);
                v___y_3858_ = v_exported_3878_;
                v_server_3859_ = v___x_3885_;
                state = 5;
                continue;
            }
            14 => {
                if v_isShared_3891_ == 0 {
                    lean_ctor_set_tag(v___x_3890_, 0);
                    v___x_3893_ = v___x_3890_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_val_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3895_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3894_ = lean_array_push(v_fst_3838_, v___x_3893_);
                v_exported_3878_ = v___x_3894_;
                state = 11;
                continue;
            }
            16 => {
                v_exportEntry_x3f_3903_ = lean_ctor_get(v_descr_3825_, 6);
                lean_inc_ref(v_exportEntry_x3f_3903_);
                lean_inc_ref(v_env_3826_);
                v___x_3904_ = lean_apply_2(v_exportEntry_x3f_3903_, v_env_3826_, v_a_3899_);
                v_exported_3905_ = lean_ctor_get(v___x_3904_, 0);
                lean_inc(v_exported_3905_);
                v_server_3906_ = lean_ctor_get(v___x_3904_, 1);
                lean_inc(v_server_3906_);
                v_private_3907_ = lean_ctor_get(v___x_3904_, 2);
                lean_inc(v_private_3907_);
                lean_dec_ref(v___x_3904_);
                if lean_obj_tag(v_exported_3905_) == 1 {
                    v_val_3933_ = lean_ctor_get(v_exported_3905_, 0);
                    lean_inc(v_val_3933_);
                    lean_dec_ref_known(v_exported_3905_, 1);
                    lean_inc(v_a_3898_);
                    v___x_3934_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3934_, 0, v_a_3898_);
                    lean_ctor_set(v___x_3934_, 1, v_val_3933_);
                    v___x_3935_ = lean_array_push(v_fst_3838_, v___x_3934_);
                    v_exported_3929_ = v___x_3935_;
                    state = 23;
                    continue;
                } else {
                    lean_dec(v_exported_3905_);
                    v_exported_3929_ = v_fst_3838_;
                    state = 23;
                    continue;
                }
            }
            17 => {
                if lean_obj_tag(v_private_3907_) == 1 {
                    v_val_3911_ = lean_ctor_get(v_private_3907_, 0);
                    lean_inc(v_val_3911_);
                    lean_dec_ref_known(v_private_3907_, 1);
                    if v_isShared_3902_ == 0 {
                        lean_ctor_set(v___x_3901_, 1, v_val_3911_);
                        v___x_3913_ = v___x_3901_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3898_);
                        lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_val_3911_);
                        v___x_3913_ = v_reuseFailAlloc_3921_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_dec(v_private_3907_);
                    lean_del_object(v___x_3901_);
                    lean_dec(v_a_3898_);
                    if v_isShared_3846_ == 0 {
                        lean_ctor_set(v___x_3845_, 0, v_server_3910_);
                        v___x_3923_ = v___x_3845_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_server_3910_);
                        lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_snd_3843_);
                        v___x_3923_ = v_reuseFailAlloc_3927_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                v___x_3914_ = lean_array_push(v_snd_3843_, v___x_3913_);
                if v_isShared_3846_ == 0 {
                    lean_ctor_set(v___x_3845_, 1, v___x_3914_);
                    lean_ctor_set(v___x_3845_, 0, v_server_3910_);
                    v___x_3916_ = v___x_3845_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_server_3910_);
                    lean_ctor_set(v_reuseFailAlloc_3920_, 1, v___x_3914_);
                    v___x_3916_ = v_reuseFailAlloc_3920_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3841_ == 0 {
                    lean_ctor_set(v___x_3840_, 1, v___x_3916_);
                    lean_ctor_set(v___x_3840_, 0, v___y_3909_);
                    v___x_3918_ = v___x_3840_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___y_3909_);
                    lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3916_);
                    v___x_3918_ = v_reuseFailAlloc_3919_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v_a_3832_ = v___x_3918_;
                state = 1;
                continue;
            }
            21 => {
                if v_isShared_3841_ == 0 {
                    lean_ctor_set(v___x_3840_, 1, v___x_3923_);
                    lean_ctor_set(v___x_3840_, 0, v___y_3909_);
                    v___x_3925_ = v___x_3840_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___y_3909_);
                    lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___x_3923_);
                    v___x_3925_ = v_reuseFailAlloc_3926_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v_a_3832_ = v___x_3925_;
                state = 1;
                continue;
            }
            23 => {
                if lean_obj_tag(v_server_3906_) == 1 {
                    v_val_3930_ = lean_ctor_get(v_server_3906_, 0);
                    lean_inc(v_val_3930_);
                    lean_dec_ref_known(v_server_3906_, 1);
                    lean_inc(v_a_3898_);
                    v___x_3931_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3931_, 0, v_a_3898_);
                    lean_ctor_set(v___x_3931_, 1, v_val_3930_);
                    v___x_3932_ = lean_array_push(v_fst_3842_, v___x_3931_);
                    v___y_3909_ = v_exported_3929_;
                    v_server_3910_ = v___x_3932_;
                    state = 17;
                    continue;
                } else {
                    lean_dec(v_server_3906_);
                    v___y_3909_ = v_exported_3929_;
                    v_server_3910_ = v_fst_3842_;
                    state = 17;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg___boxed(
    mut v_descr_3939_: *mut LeanObject,
    mut v_env_3940_: *mut LeanObject,
    mut v_as_3941_: *mut LeanObject,
    mut v_sz_3942_: *mut LeanObject,
    mut v_i_3943_: *mut LeanObject,
    mut v_b_3944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3945_: usize = 0;
    let mut v_i_boxed_3946_: usize = 0;
    let mut v_res_3947_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3942_);
    lean_dec(v_sz_3942_);
    v_i_boxed_3946_ = lean_unbox_usize(v_i_3943_);
    lean_dec(v_i_3943_);
    v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_3939_, v_env_3940_, v_as_3941_, v_sz_boxed_3945_, v_i_boxed_3946_, v_b_3944_);
    lean_dec_ref(v_as_3941_);
    return v_res_3947_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(
    mut v_descr_3955_: *mut LeanObject,
    mut v_env_3956_: *mut LeanObject,
    mut v_s_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_newEntries_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3961_: u8 = 0;
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3965_: usize = 0;
    let mut v___x_3966_: usize = 0;
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut v_unused_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_newEntries_3958_ = lean_ctor_get(v_s_3957_, 2);
                v_isSharedCheck_3975_ = (!lean_is_exclusive(v_s_3957_)) as u8;
                if v_isSharedCheck_3975_ == 0 {
                    v_unused_3976_ = lean_ctor_get(v_s_3957_, 1);
                    lean_dec(v_unused_3976_);
                    v_unused_3977_ = lean_ctor_get(v_s_3957_, 0);
                    lean_dec(v_unused_3977_);
                    v___x_3960_ = v_s_3957_;
                    v_isShared_3961_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_newEntries_3958_);
                    lean_dec(v_s_3957_);
                    v___x_3960_ = lean_box(0);
                    v_isShared_3961_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3962_ = lean_array_mk(v_newEntries_3958_);
                v___x_3963_ = l_Array_reverse___redArg(v___x_3962_);
                v___x_3964_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__2;
                v_sz_3965_ = lean_array_size(v___x_3963_);
                v___x_3966_ = 0usize;
                v___x_3967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_3955_, v_env_3956_, v___x_3963_, v_sz_3965_, v___x_3966_, v___x_3964_);
                lean_dec_ref(v___x_3963_);
                v_snd_3968_ = lean_ctor_get(v___x_3967_, 1);
                lean_inc(v_snd_3968_);
                v_fst_3969_ = lean_ctor_get(v___x_3967_, 0);
                lean_inc(v_fst_3969_);
                lean_dec_ref(v___x_3967_);
                v_fst_3970_ = lean_ctor_get(v_snd_3968_, 0);
                lean_inc(v_fst_3970_);
                v_snd_3971_ = lean_ctor_get(v_snd_3968_, 1);
                lean_inc(v_snd_3971_);
                lean_dec(v_snd_3968_);
                if v_isShared_3961_ == 0 {
                    lean_ctor_set(v___x_3960_, 2, v_snd_3971_);
                    lean_ctor_set(v___x_3960_, 1, v_fst_3970_);
                    lean_ctor_set(v___x_3960_, 0, v_fst_3969_);
                    v___x_3973_ = v___x_3960_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_fst_3969_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_fst_3970_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_snd_3971_);
                    v___x_3973_ = v_reuseFailAlloc_3974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_exportEntriesFn(
    mut v_00_u03b1_3978_: *mut LeanObject,
    mut v_00_u03b2_3979_: *mut LeanObject,
    mut v_00_u03c3_3980_: *mut LeanObject,
    mut v_descr_3981_: *mut LeanObject,
    mut v_env_3982_: *mut LeanObject,
    mut v_s_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    v___x_3984_ =
        l_Lean_ScopedEnvExtension_exportEntriesFn___redArg(v_descr_3981_, v_env_3982_, v_s_3983_);
    return v___x_3984_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(
    mut v_00_u03b1_3985_: *mut LeanObject,
    mut v_00_u03b2_3986_: *mut LeanObject,
    mut v_00_u03c3_3987_: *mut LeanObject,
    mut v_descr_3988_: *mut LeanObject,
    mut v_env_3989_: *mut LeanObject,
    mut v_as_3990_: *mut LeanObject,
    mut v_sz_3991_: usize,
    mut v_i_3992_: usize,
    mut v_b_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___redArg(v_descr_3988_, v_env_3989_, v_as_3990_, v_sz_3991_, v_i_3992_, v_b_3993_);
    return v___x_3994_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0___boxed(
    mut v_00_u03b1_3995_: *mut LeanObject,
    mut v_00_u03b2_3996_: *mut LeanObject,
    mut v_00_u03c3_3997_: *mut LeanObject,
    mut v_descr_3998_: *mut LeanObject,
    mut v_env_3999_: *mut LeanObject,
    mut v_as_4000_: *mut LeanObject,
    mut v_sz_4001_: *mut LeanObject,
    mut v_i_4002_: *mut LeanObject,
    mut v_b_4003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4004_: usize = 0;
    let mut v_i_boxed_4005_: usize = 0;
    let mut v_res_4006_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4004_ = lean_unbox_usize(v_sz_4001_);
    lean_dec(v_sz_4001_);
    v_i_boxed_4005_ = lean_unbox_usize(v_i_4002_);
    lean_dec(v_i_4002_);
    v_res_4006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_ScopedEnvExtension_exportEntriesFn_spec__0(v_00_u03b1_3995_, v_00_u03b2_3996_, v_00_u03c3_3997_, v_descr_3998_, v_env_3999_, v_as_4000_, v_sz_boxed_4004_, v_i_boxed_4005_, v_b_4003_);
    lean_dec_ref(v_as_4000_);
    return v_res_4006_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(
    mut v_x_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    v___x_4010_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__0___closed__1;
    v___x_4011_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4011_, 0, v___x_4010_);
    return v___x_4011_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4___boxed(
    mut v_x_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
    mut v___y_4014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4015_: *mut LeanObject = core::ptr::null_mut();
    v_res_4015_ =
        l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__4(v_x_4012_, v___y_4013_);
    lean_dec_ref(v___y_4013_);
    lean_dec_ref(v_x_4012_);
    return v_res_4015_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(
    mut v_s_4016_: *mut LeanObject,
    mut v_x_4017_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_4016_);
    return v_s_4016_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0___boxed(
    mut v_s_4018_: *mut LeanObject,
    mut v_x_4019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4020_: *mut LeanObject = core::ptr::null_mut();
    v_res_4020_ =
        l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__0(v_s_4018_, v_x_4019_);
    lean_dec_ref(v_x_4019_);
    lean_dec_ref(v_s_4018_);
    return v_res_4020_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(
    mut v_x_4023_: *mut LeanObject,
    mut v_x_4024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    v___x_4025_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___closed__0;
    return v___x_4025_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1___boxed(
    mut v_x_4026_: *mut LeanObject,
    mut v_x_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4028_: *mut LeanObject = core::ptr::null_mut();
    v_res_4028_ =
        l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__1(v_x_4026_, v_x_4027_);
    lean_dec_ref(v_x_4027_);
    lean_dec_ref(v_x_4026_);
    return v_res_4028_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(
    mut v_x_4029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    v___x_4030_ = lean_box(0);
    return v___x_4030_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2___boxed(
    mut v_x_4031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4032_: *mut LeanObject = core::ptr::null_mut();
    v_res_4032_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___lam__2(v_x_4031_);
    lean_dec_ref(v_x_4031_);
    return v_res_4032_;
}
pub unsafe fn _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
    return v___x_4037_;
}
pub unsafe fn _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5()
-> *mut LeanObject {
    let mut v___f_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    v___f_4038_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__3;
    v___f_4039_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__2;
    v___f_4040_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__1;
    v___f_4041_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__0;
    v___x_4042_ = lean_box(0);
    v___x_4043_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4_once
        ),
        _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__4,
    );
    v___x_4044_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4044_, 0, v___x_4043_);
    lean_ctor_set(v___x_4044_, 1, v___x_4042_);
    lean_ctor_set(v___x_4044_, 2, v___f_4041_);
    lean_ctor_set(v___x_4044_, 3, v___f_4040_);
    lean_ctor_set(v___x_4044_, 4, v___f_4039_);
    lean_ctor_set(v___x_4044_, 5, v___f_4038_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default___redArg(
    mut v_inst_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    v___f_4046_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__0;
    v___f_4047_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4047_, 0, v_inst_4045_);
    v___f_4048_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__1;
    v___f_4049_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__2;
    v___x_4050_ = lean_box(0);
    v___x_4051_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3_once
        ),
        _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__3,
    );
    v___x_4052_ = l_Lean_ScopedEnvExtension_instInhabitedDescr___redArg___closed__4;
    v___x_4053_ = lean_alloc_ctor(0, 7, (0) as u32);
    lean_ctor_set(v___x_4053_, 0, v___x_4050_);
    lean_ctor_set(v___x_4053_, 1, v___x_4051_);
    lean_ctor_set(v___x_4053_, 2, v___f_4046_);
    lean_ctor_set(v___x_4053_, 3, v___f_4047_);
    lean_ctor_set(v___x_4053_, 4, v___f_4048_);
    lean_ctor_set(v___x_4053_, 5, v___x_4052_);
    lean_ctor_set(v___x_4053_, 6, v___f_4049_);
    v___x_4054_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5_once
        ),
        _init_l_Lean_instInhabitedScopedEnvExtension_default___redArg___closed__5,
    );
    v___x_4055_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4055_, 0, v___x_4053_);
    lean_ctor_set(v___x_4055_, 1, v___x_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension_default(
    mut v_00_u03b1_4056_: *mut LeanObject,
    mut v_00_u03b2_4057_: *mut LeanObject,
    mut v_00_u03c3_4058_: *mut LeanObject,
    mut v_inst_4059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    v___x_4060_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_4059_);
    return v___x_4060_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension___redArg(
    mut v_inst_4061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_4061_);
    return v___x_4062_;
}
pub unsafe fn l_Lean_instInhabitedScopedEnvExtension(
    mut v_a_4063_: *mut LeanObject,
    mut v_inst_4064_: *mut LeanObject,
    mut v_a_4065_: *mut LeanObject,
    mut v_a_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    v___x_4067_ = l_Lean_instInhabitedScopedEnvExtension_default___redArg(v_inst_4064_);
    return v___x_4067_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    v___x_4071_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn___closed__0_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_;
    v___x_4072_ = lean_st_mk_ref(v___x_4071_);
    v___x_4073_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4073_, 0, v___x_4072_);
    return v___x_4073_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2____boxed(
    mut v_a_4074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4075_: *mut LeanObject = core::ptr::null_mut();
    v_res_4075_ = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
    return v_res_4075_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(
    mut v_s_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_newEntries_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    v_newEntries_4080_ = lean_ctor_get(v_s_4079_, 2);
    v___x_4081_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___closed__1;
    v___x_4082_ = l_List_lengthTR___redArg(v_newEntries_4080_);
    v___x_4083_ = l_Nat_reprFast(v___x_4082_);
    v___x_4084_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4084_, 0, v___x_4083_);
    v___x_4085_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4085_, 0, v___x_4081_);
    lean_ctor_set(v___x_4085_, 1, v___x_4084_);
    return v___x_4085_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0___boxed(
    mut v_s_4086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4087_: *mut LeanObject = core::ptr::null_mut();
    v_res_4087_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__0(v_s_4086_);
    lean_dec_ref(v_s_4086_);
    return v_res_4087_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(
    mut v_x_4088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    v___x_4089_ = l_Lean_ScopedEnvExtension_exportEntriesFn___redArg___closed__0;
    return v___x_4089_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1___boxed(
    mut v_x_4090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4091_: *mut LeanObject = core::ptr::null_mut();
    v_res_4091_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___lam__1(v_x_4090_);
    lean_dec_ref(v_x_4090_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg(
    mut v_descr_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4111_: u8 = 0;
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4120_: u8 = 0;
    let mut v_a_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4096_ = lean_ctor_get(v_descr_4094_, 0);
                v___f_4097_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__0;
                v___f_4098_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg___closed__1;
                lean_inc_ref_n(v_descr_4094_, 4);
                v___x_4099_ = lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_mkInitial___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___x_4099_, 0, lean_box(0));
                lean_closure_set(v___x_4099_, 1, lean_box(0));
                lean_closure_set(v___x_4099_, 2, lean_box(0));
                lean_closure_set(v___x_4099_, 3, v_descr_4094_);
                v___x_4100_ = lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_addImportedFn___boxed as *mut core::ffi::c_void,
                    7,
                    4,
                );
                lean_closure_set(v___x_4100_, 0, lean_box(0));
                lean_closure_set(v___x_4100_, 1, lean_box(0));
                lean_closure_set(v___x_4100_, 2, lean_box(0));
                lean_closure_set(v___x_4100_, 3, v_descr_4094_);
                v___x_4101_ = lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_addEntryFn as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___x_4101_, 0, lean_box(0));
                lean_closure_set(v___x_4101_, 1, lean_box(0));
                lean_closure_set(v___x_4101_, 2, lean_box(0));
                lean_closure_set(v___x_4101_, 3, v_descr_4094_);
                v___x_4102_ = lean_alloc_closure(
                    l_Lean_ScopedEnvExtension_exportEntriesFn as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___x_4102_, 0, lean_box(0));
                lean_closure_set(v___x_4102_, 1, lean_box(0));
                lean_closure_set(v___x_4102_, 2, lean_box(0));
                lean_closure_set(v___x_4102_, 3, v_descr_4094_);
                v___x_4103_ = lean_box(2);
                v___x_4104_ = lean_box(0);
                lean_inc(v_name_4096_);
                v___x_4105_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_4105_, 0, v_name_4096_);
                lean_ctor_set(v___x_4105_, 1, v___x_4099_);
                lean_ctor_set(v___x_4105_, 2, v___x_4100_);
                lean_ctor_set(v___x_4105_, 3, v___x_4101_);
                lean_ctor_set(v___x_4105_, 4, v___x_4102_);
                lean_ctor_set(v___x_4105_, 5, v___f_4097_);
                lean_ctor_set(v___x_4105_, 6, v___x_4103_);
                lean_ctor_set(v___x_4105_, 7, v___x_4104_);
                v___x_4106_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4106_, 0, v___x_4105_);
                lean_ctor_set(v___x_4106_, 1, v___f_4098_);
                v___x_4107_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4106_);
                if lean_obj_tag(v___x_4107_) == 0 {
                    v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
                    v_isSharedCheck_4120_ = (!lean_is_exclusive(v___x_4107_)) as u8;
                    if v_isSharedCheck_4120_ == 0 {
                        v___x_4110_ = v___x_4107_;
                        v_isShared_4111_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4108_);
                        lean_dec(v___x_4107_);
                        v___x_4110_ = lean_box(0);
                        v_isShared_4111_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_descr_4094_);
                    v_a_4121_ = lean_ctor_get(v___x_4107_, 0);
                    v_isSharedCheck_4128_ = (!lean_is_exclusive(v___x_4107_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4123_ = v___x_4107_;
                        v_isShared_4124_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4121_);
                        lean_dec(v___x_4107_);
                        v___x_4123_ = lean_box(0);
                        v_isShared_4124_ = v_isSharedCheck_4128_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4112_ = l_Lean_scopedEnvExtensionsRef;
                v___x_4113_ = lean_st_ref_take(v___x_4112_);
                v___x_4114_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4114_, 0, v_descr_4094_);
                lean_ctor_set(v___x_4114_, 1, v_a_4108_);
                lean_inc_ref(v___x_4114_);
                v___x_4115_ = lean_array_push(v___x_4113_, v___x_4114_);
                v___x_4116_ = lean_st_ref_set(v___x_4112_, v___x_4115_);
                if v_isShared_4111_ == 0 {
                    lean_ctor_set(v___x_4110_, 0, v___x_4114_);
                    v___x_4118_ = v___x_4110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4114_);
                    v___x_4118_ = v_reuseFailAlloc_4119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4118_;
            }
            3 => {
                if v_isShared_4124_ == 0 {
                    v___x_4126_ = v___x_4123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
                    v___x_4126_ = v_reuseFailAlloc_4127_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___redArg___boxed(
    mut v_descr_4129_: *mut LeanObject,
    mut v_a_4130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4131_: *mut LeanObject = core::ptr::null_mut();
    v_res_4131_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_4129_);
    return v_res_4131_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe(
    mut v_00_u03b1_4132_: *mut LeanObject,
    mut v_00_u03b2_4133_: *mut LeanObject,
    mut v_00_u03c3_4134_: *mut LeanObject,
    mut v_descr_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v_descr_4135_);
    return v___x_4137_;
}
pub unsafe fn l_Lean_registerScopedEnvExtensionUnsafe___boxed(
    mut v_00_u03b1_4138_: *mut LeanObject,
    mut v_00_u03b2_4139_: *mut LeanObject,
    mut v_00_u03c3_4140_: *mut LeanObject,
    mut v_descr_4141_: *mut LeanObject,
    mut v_a_4142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4143_: *mut LeanObject = core::ptr::null_mut();
    v_res_4143_ = l_Lean_registerScopedEnvExtensionUnsafe(
        v_00_u03b1_4138_,
        v_00_u03b2_4139_,
        v_00_u03c3_4140_,
        v_descr_4141_,
    );
    return v_res_4143_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_pushScope___redArg___lam__0(
    mut v_s_4144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stateStack_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v_state_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4156_: u8 = 0;
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v_isSharedCheck_4166_: u8 = 0;
    let mut v_unused_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4145_ = lean_ctor_get(v_s_4144_, 0);
                if lean_obj_tag(v_stateStack_4145_) == 0 {
                    return v_s_4144_;
                } else {
                    lean_inc_ref(v_stateStack_4145_);
                    v_head_4146_ = lean_ctor_get(v_stateStack_4145_, 0);
                    lean_inc(v_head_4146_);
                    v_scopedEntries_4147_ = lean_ctor_get(v_s_4144_, 1);
                    v_newEntries_4148_ = lean_ctor_get(v_s_4144_, 2);
                    v_isSharedCheck_4166_ = (!lean_is_exclusive(v_s_4144_)) as u8;
                    if v_isSharedCheck_4166_ == 0 {
                        v_unused_4167_ = lean_ctor_get(v_s_4144_, 0);
                        lean_dec(v_unused_4167_);
                        v___x_4150_ = v_s_4144_;
                        v_isShared_4151_ = v_isSharedCheck_4166_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_newEntries_4148_);
                        lean_inc(v_scopedEntries_4147_);
                        lean_dec(v_s_4144_);
                        v___x_4150_ = lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4166_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_state_4152_ = lean_ctor_get(v_head_4146_, 0);
                v_activeScopes_4153_ = lean_ctor_get(v_head_4146_, 1);
                v_isSharedCheck_4165_ = (!lean_is_exclusive(v_head_4146_)) as u8;
                if v_isSharedCheck_4165_ == 0 {
                    v___x_4155_ = v_head_4146_;
                    v_isShared_4156_ = v_isSharedCheck_4165_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_activeScopes_4153_);
                    lean_inc(v_state_4152_);
                    lean_dec(v_head_4146_);
                    v___x_4155_ = lean_box(0);
                    v_isShared_4156_ = v_isSharedCheck_4165_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4157_ = 1;
                if v_isShared_4156_ == 0 {
                    v___x_4159_ = v___x_4155_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_state_4152_);
                    lean_ctor_set(v_reuseFailAlloc_4164_, 1, v_activeScopes_4153_);
                    v___x_4159_ = v_reuseFailAlloc_4164_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_4159_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_4157_,
                );
                v___x_4160_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4160_, 0, v___x_4159_);
                lean_ctor_set(v___x_4160_, 1, v_stateStack_4145_);
                if v_isShared_4151_ == 0 {
                    lean_ctor_set(v___x_4150_, 0, v___x_4160_);
                    v___x_4162_ = v___x_4150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
                    lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_scopedEntries_4147_);
                    lean_ctor_set(v_reuseFailAlloc_4163_, 2, v_newEntries_4148_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_pushScope___redArg(
    mut v_ext_4169_: *mut LeanObject,
    mut v_env_4170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4171_ = lean_ctor_get(v_ext_4169_, 1);
    lean_inc_ref(v_ext_4171_);
    lean_dec_ref(v_ext_4169_);
    v___f_4172_ = l_Lean_ScopedEnvExtension_pushScope___redArg___closed__0;
    v___x_4173_ = lean_box(1);
    v___x_4174_ = lean_box(0);
    v___x_4175_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4171_,
        v_env_4170_,
        v___f_4172_,
        v___x_4173_,
        v___x_4174_,
    );
    return v___x_4175_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_pushScope(
    mut v_00_u03b1_4176_: *mut LeanObject,
    mut v_00_u03b2_4177_: *mut LeanObject,
    mut v_00_u03c3_4178_: *mut LeanObject,
    mut v_ext_4179_: *mut LeanObject,
    mut v_env_4180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    v___x_4181_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v_ext_4179_, v_env_4180_);
    return v___x_4181_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_popScope___redArg___lam__0(
    mut v_s_4182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stateStack_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4193_: u8 = 0;
    let mut v_unused_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4183_ = lean_ctor_get(v_s_4182_, 0);
                if lean_obj_tag(v_stateStack_4183_) == 1 {
                    v_tail_4184_ = lean_ctor_get(v_stateStack_4183_, 1);
                    if lean_obj_tag(v_tail_4184_) == 1 {
                        lean_inc_ref(v_tail_4184_);
                        v_scopedEntries_4185_ = lean_ctor_get(v_s_4182_, 1);
                        v_newEntries_4186_ = lean_ctor_get(v_s_4182_, 2);
                        v_isSharedCheck_4193_ = (!lean_is_exclusive(v_s_4182_)) as u8;
                        if v_isSharedCheck_4193_ == 0 {
                            v_unused_4194_ = lean_ctor_get(v_s_4182_, 0);
                            lean_dec(v_unused_4194_);
                            v___x_4188_ = v_s_4182_;
                            v_isShared_4189_ = v_isSharedCheck_4193_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_newEntries_4186_);
                            lean_inc(v_scopedEntries_4185_);
                            lean_dec(v_s_4182_);
                            v___x_4188_ = lean_box(0);
                            v_isShared_4189_ = v_isSharedCheck_4193_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v_s_4182_;
                    }
                } else {
                    return v_s_4182_;
                }
            }
            1 => {
                if v_isShared_4189_ == 0 {
                    lean_ctor_set(v___x_4188_, 0, v_tail_4184_);
                    v___x_4191_ = v___x_4188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_tail_4184_);
                    lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_scopedEntries_4185_);
                    lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_newEntries_4186_);
                    v___x_4191_ = v_reuseFailAlloc_4192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_popScope___redArg(
    mut v_ext_4196_: *mut LeanObject,
    mut v_env_4197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4198_ = lean_ctor_get(v_ext_4196_, 1);
    lean_inc_ref(v_ext_4198_);
    lean_dec_ref(v_ext_4196_);
    v___f_4199_ = l_Lean_ScopedEnvExtension_popScope___redArg___closed__0;
    v___x_4200_ = lean_box(1);
    v___x_4201_ = lean_box(0);
    v___x_4202_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4198_,
        v_env_4197_,
        v___f_4199_,
        v___x_4200_,
        v___x_4201_,
    );
    return v___x_4202_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_popScope(
    mut v_00_u03b1_4203_: *mut LeanObject,
    mut v_00_u03b2_4204_: *mut LeanObject,
    mut v_00_u03c3_4205_: *mut LeanObject,
    mut v_ext_4206_: *mut LeanObject,
    mut v_env_4207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    v___x_4208_ = l_Lean_ScopedEnvExtension_popScope___redArg(v_ext_4206_, v_env_4207_);
    return v___x_4208_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(
    mut v_a_4209_: *mut LeanObject,
    mut v_a_4210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4212_: u8 = 0;
    let mut v_head_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v_state_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4222_: u8 = 0;
    let mut v_one_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4232_: u8 = 0;
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4211_ = lean_unsigned_to_nat(0);
                v_isZero_4212_ = lean_nat_dec_eq(v_a_4209_, v_zero_4211_);
                if v_isZero_4212_ == 1 {
                    return v_a_4210_;
                } else {
                    if lean_obj_tag(v_a_4210_) == 0 {
                        return v_a_4210_;
                    } else {
                        v_head_4213_ = lean_ctor_get(v_a_4210_, 0);
                        v_tail_4214_ = lean_ctor_get(v_a_4210_, 1);
                        v_isSharedCheck_4233_ = (!lean_is_exclusive(v_a_4210_)) as u8;
                        if v_isSharedCheck_4233_ == 0 {
                            v___x_4216_ = v_a_4210_;
                            v_isShared_4217_ = v_isSharedCheck_4233_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_4214_);
                            lean_inc(v_head_4213_);
                            lean_dec(v_a_4210_);
                            v___x_4216_ = lean_box(0);
                            v_isShared_4217_ = v_isSharedCheck_4233_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_state_4218_ = lean_ctor_get(v_head_4213_, 0);
                v_activeScopes_4219_ = lean_ctor_get(v_head_4213_, 1);
                v_isSharedCheck_4232_ = (!lean_is_exclusive(v_head_4213_)) as u8;
                if v_isSharedCheck_4232_ == 0 {
                    v___x_4221_ = v_head_4213_;
                    v_isShared_4222_ = v_isSharedCheck_4232_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_activeScopes_4219_);
                    lean_inc(v_state_4218_);
                    lean_dec(v_head_4213_);
                    v___x_4221_ = lean_box(0);
                    v_isShared_4222_ = v_isSharedCheck_4232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_one_4223_ = lean_unsigned_to_nat(1);
                v_n_4224_ = lean_nat_sub(v_a_4209_, v_one_4223_);
                if v_isShared_4222_ == 0 {
                    v___x_4226_ = v___x_4221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_state_4218_);
                    lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_activeScopes_4219_);
                    v___x_4226_ = v_reuseFailAlloc_4231_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_4226_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_isZero_4212_,
                );
                v___x_4227_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_n_4224_, v_tail_4214_);
                lean_dec(v_n_4224_);
                if v_isShared_4217_ == 0 {
                    lean_ctor_set(v___x_4216_, 1, v___x_4227_);
                    lean_ctor_set(v___x_4216_, 0, v___x_4226_);
                    v___x_4229_ = v___x_4216_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4226_);
                    lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4227_);
                    v___x_4229_ = v_reuseFailAlloc_4230_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg___boxed(
    mut v_a_4234_: *mut LeanObject,
    mut v_a_4235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4236_: *mut LeanObject = core::ptr::null_mut();
    v_res_4236_ =
        l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(
            v_a_4234_, v_a_4235_,
        );
    lean_dec(v_a_4234_);
    return v_res_4236_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(
    mut v_00_u03c3_4237_: *mut LeanObject,
    mut v_a_4238_: *mut LeanObject,
    mut v_a_4239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    v___x_4240_ =
        l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(
            v_a_4238_, v_a_4239_,
        );
    return v___x_4240_;
}
pub unsafe fn l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___boxed(
    mut v_00_u03c3_4241_: *mut LeanObject,
    mut v_a_4242_: *mut LeanObject,
    mut v_a_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4244_: *mut LeanObject = core::ptr::null_mut();
    v_res_4244_ =
        l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go(
            v_00_u03c3_4241_,
            v_a_4242_,
            v_a_4243_,
        );
    lean_dec(v_a_4242_);
    return v_res_4244_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(
    mut v_depth_4245_: *mut LeanObject,
    mut v_s_4246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stateStack_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4252_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4247_ = lean_ctor_get(v_s_4246_, 0);
                v_scopedEntries_4248_ = lean_ctor_get(v_s_4246_, 1);
                v_newEntries_4249_ = lean_ctor_get(v_s_4246_, 2);
                v_isSharedCheck_4257_ = (!lean_is_exclusive(v_s_4246_)) as u8;
                if v_isSharedCheck_4257_ == 0 {
                    v___x_4251_ = v_s_4246_;
                    v_isShared_4252_ = v_isSharedCheck_4257_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_newEntries_4249_);
                    lean_inc(v_scopedEntries_4248_);
                    lean_inc(v_stateStack_4247_);
                    lean_dec(v_s_4246_);
                    v___x_4251_ = lean_box(0);
                    v_isShared_4252_ = v_isSharedCheck_4257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4253_ = l___private_Lean_ScopedEnvExtension_0__Lean_ScopedEnvExtension_setDelimitsLocal_go___redArg(v_depth_4245_, v_stateStack_4247_);
                if v_isShared_4252_ == 0 {
                    lean_ctor_set(v___x_4251_, 0, v___x_4253_);
                    v___x_4255_ = v___x_4251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4253_);
                    lean_ctor_set(v_reuseFailAlloc_4256_, 1, v_scopedEntries_4248_);
                    lean_ctor_set(v_reuseFailAlloc_4256_, 2, v_newEntries_4249_);
                    v___x_4255_ = v_reuseFailAlloc_4256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed(
    mut v_depth_4258_: *mut LeanObject,
    mut v_s_4259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4260_: *mut LeanObject = core::ptr::null_mut();
    v_res_4260_ =
        l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0(v_depth_4258_, v_s_4259_);
    lean_dec(v_depth_4258_);
    return v_res_4260_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(
    mut v_ext_4261_: *mut LeanObject,
    mut v_env_4262_: *mut LeanObject,
    mut v_depth_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4264_ = lean_ctor_get(v_ext_4261_, 1);
    lean_inc_ref(v_ext_4264_);
    lean_dec_ref(v_ext_4261_);
    v___f_4265_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4265_, 0, v_depth_4263_);
    v___x_4266_ = lean_box(1);
    v___x_4267_ = lean_box(0);
    v___x_4268_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4264_,
        v_env_4262_,
        v___f_4265_,
        v___x_4266_,
        v___x_4267_,
    );
    return v___x_4268_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_setDelimitsLocal(
    mut v_00_u03b1_4269_: *mut LeanObject,
    mut v_00_u03b2_4270_: *mut LeanObject,
    mut v_00_u03c3_4271_: *mut LeanObject,
    mut v_ext_4272_: *mut LeanObject,
    mut v_env_4273_: *mut LeanObject,
    mut v_depth_4274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    v___x_4275_ = l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(
        v_ext_4272_,
        v_env_4273_,
        v_depth_4274_,
    );
    return v___x_4275_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntry___redArg(
    mut v_ext_4276_: *mut LeanObject,
    mut v_env_4277_: *mut LeanObject,
    mut v_b_4278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4279_ = lean_ctor_get(v_ext_4276_, 1);
    lean_inc_ref(v_ext_4279_);
    lean_dec_ref(v_ext_4276_);
    v_toEnvExtension_4280_ = lean_ctor_get(v_ext_4279_, 0);
    v_asyncMode_4281_ = lean_ctor_get(v_toEnvExtension_4280_, 2);
    lean_inc(v_asyncMode_4281_);
    v___x_4282_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4282_, 0, v_b_4278_);
    v___x_4283_ = lean_box(0);
    v___x_4284_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
        v_ext_4279_,
        v_env_4277_,
        v___x_4282_,
        v_asyncMode_4281_,
        v___x_4283_,
    );
    lean_dec(v_asyncMode_4281_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addEntry(
    mut v_00_u03b1_4285_: *mut LeanObject,
    mut v_00_u03b2_4286_: *mut LeanObject,
    mut v_00_u03c3_4287_: *mut LeanObject,
    mut v_ext_4288_: *mut LeanObject,
    mut v_env_4289_: *mut LeanObject,
    mut v_b_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    v___x_4291_ = l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_4288_, v_env_4289_, v_b_4290_);
    return v___x_4291_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addScopedEntry___redArg(
    mut v_ext_4292_: *mut LeanObject,
    mut v_env_4293_: *mut LeanObject,
    mut v_namespaceName_4294_: *mut LeanObject,
    mut v_b_4295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4299_: u8 = 0;
    let mut v_toEnvExtension_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4307_: u8 = 0;
    let mut v_unused_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ext_4296_ = lean_ctor_get(v_ext_4292_, 1);
                v_isSharedCheck_4307_ = (!lean_is_exclusive(v_ext_4292_)) as u8;
                if v_isSharedCheck_4307_ == 0 {
                    v_unused_4308_ = lean_ctor_get(v_ext_4292_, 0);
                    lean_dec(v_unused_4308_);
                    v___x_4298_ = v_ext_4292_;
                    v_isShared_4299_ = v_isSharedCheck_4307_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ext_4296_);
                    lean_dec(v_ext_4292_);
                    v___x_4298_ = lean_box(0);
                    v_isShared_4299_ = v_isSharedCheck_4307_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toEnvExtension_4300_ = lean_ctor_get(v_ext_4296_, 0);
                v_asyncMode_4301_ = lean_ctor_get(v_toEnvExtension_4300_, 2);
                lean_inc(v_asyncMode_4301_);
                if v_isShared_4299_ == 0 {
                    lean_ctor_set_tag(v___x_4298_, 1);
                    lean_ctor_set(v___x_4298_, 1, v_b_4295_);
                    lean_ctor_set(v___x_4298_, 0, v_namespaceName_4294_);
                    v___x_4303_ = v___x_4298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_namespaceName_4294_);
                    lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_b_4295_);
                    v___x_4303_ = v_reuseFailAlloc_4306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4304_ = lean_box(0);
                v___x_4305_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_4296_,
                    v_env_4293_,
                    v___x_4303_,
                    v_asyncMode_4301_,
                    v___x_4304_,
                );
                lean_dec(v_asyncMode_4301_);
                return v___x_4305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addScopedEntry(
    mut v_00_u03b1_4309_: *mut LeanObject,
    mut v_00_u03b2_4310_: *mut LeanObject,
    mut v_00_u03c3_4311_: *mut LeanObject,
    mut v_ext_4312_: *mut LeanObject,
    mut v_env_4313_: *mut LeanObject,
    mut v_namespaceName_4314_: *mut LeanObject,
    mut v_b_4315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    v___x_4316_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(
        v_ext_4312_,
        v_env_4313_,
        v_namespaceName_4314_,
        v_b_4315_,
    );
    return v___x_4316_;
}
pub unsafe fn l_Lean_stateStackModify___redArg(
    mut v_ext_4317_: *mut LeanObject,
    mut v_states_4318_: *mut LeanObject,
    mut v_b_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_descr_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v_addEntry_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_4329_: u8 = 0;
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_top_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_states_4318_) == 0 {
                    lean_dec(v_b_4319_);
                    lean_dec_ref(v_ext_4317_);
                    return v_states_4318_;
                } else {
                    v_descr_4320_ = lean_ctor_get(v_ext_4317_, 0);
                    v_head_4321_ = lean_ctor_get(v_states_4318_, 0);
                    v_tail_4322_ = lean_ctor_get(v_states_4318_, 1);
                    v_isSharedCheck_4345_ = (!lean_is_exclusive(v_states_4318_)) as u8;
                    if v_isSharedCheck_4345_ == 0 {
                        v___x_4324_ = v_states_4318_;
                        v_isShared_4325_ = v_isSharedCheck_4345_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4322_);
                        lean_inc(v_head_4321_);
                        lean_dec(v_states_4318_);
                        v___x_4324_ = lean_box(0);
                        v_isShared_4325_ = v_isSharedCheck_4345_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4326_ = lean_ctor_get(v_descr_4320_, 4);
                v_state_4327_ = lean_ctor_get(v_head_4321_, 0);
                v_activeScopes_4328_ = lean_ctor_get(v_head_4321_, 1);
                v_delimitsLocal_4329_ = lean_ctor_get_uint8(
                    v_head_4321_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_4344_ = (!lean_is_exclusive(v_head_4321_)) as u8;
                if v_isSharedCheck_4344_ == 0 {
                    v___x_4331_ = v_head_4321_;
                    v_isShared_4332_ = v_isSharedCheck_4344_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_activeScopes_4328_);
                    lean_inc(v_state_4327_);
                    lean_dec(v_head_4321_);
                    v___x_4331_ = lean_box(0);
                    v_isShared_4332_ = v_isSharedCheck_4344_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_addEntry_4326_);
                lean_inc(v_b_4319_);
                v___x_4333_ = lean_apply_2(v_addEntry_4326_, v_state_4327_, v_b_4319_);
                if v_isShared_4332_ == 0 {
                    lean_ctor_set(v___x_4331_, 0, v___x_4333_);
                    v_top_4335_ = v___x_4331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4333_);
                    lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_activeScopes_4328_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4343_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_delimitsLocal_4329_,
                    );
                    v_top_4335_ = v_reuseFailAlloc_4343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_delimitsLocal_4329_ == 0 {
                    v___x_4336_ =
                        l_Lean_stateStackModify___redArg(v_ext_4317_, v_tail_4322_, v_b_4319_);
                    if v_isShared_4325_ == 0 {
                        lean_ctor_set(v___x_4324_, 1, v___x_4336_);
                        lean_ctor_set(v___x_4324_, 0, v_top_4335_);
                        v___x_4338_ = v___x_4324_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_top_4335_);
                        lean_ctor_set(v_reuseFailAlloc_4339_, 1, v___x_4336_);
                        v___x_4338_ = v_reuseFailAlloc_4339_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_b_4319_);
                    lean_dec_ref(v_ext_4317_);
                    if v_isShared_4325_ == 0 {
                        lean_ctor_set(v___x_4324_, 0, v_top_4335_);
                        v___x_4341_ = v___x_4324_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_top_4335_);
                        lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_tail_4322_);
                        v___x_4341_ = v_reuseFailAlloc_4342_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4338_;
            }
            5 => {
                return v___x_4341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_stateStackModify(
    mut v_00_u03b1_4346_: *mut LeanObject,
    mut v_00_u03b2_4347_: *mut LeanObject,
    mut v_00_u03c3_4348_: *mut LeanObject,
    mut v_ext_4349_: *mut LeanObject,
    mut v_states_4350_: *mut LeanObject,
    mut v_b_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    v___x_4352_ = l_Lean_stateStackModify___redArg(v_ext_4349_, v_states_4350_, v_b_4351_);
    return v___x_4352_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0(
    mut v_ext_4353_: *mut LeanObject,
    mut v_b_4354_: *mut LeanObject,
    mut v_s_4355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stateStack_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4361_: u8 = 0;
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4356_ = lean_ctor_get(v_s_4355_, 0);
                v_scopedEntries_4357_ = lean_ctor_get(v_s_4355_, 1);
                v_newEntries_4358_ = lean_ctor_get(v_s_4355_, 2);
                v_isSharedCheck_4366_ = (!lean_is_exclusive(v_s_4355_)) as u8;
                if v_isSharedCheck_4366_ == 0 {
                    v___x_4360_ = v_s_4355_;
                    v_isShared_4361_ = v_isSharedCheck_4366_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_newEntries_4358_);
                    lean_inc(v_scopedEntries_4357_);
                    lean_inc(v_stateStack_4356_);
                    lean_dec(v_s_4355_);
                    v___x_4360_ = lean_box(0);
                    v_isShared_4361_ = v_isSharedCheck_4366_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4362_ =
                    l_Lean_stateStackModify___redArg(v_ext_4353_, v_stateStack_4356_, v_b_4354_);
                if v_isShared_4361_ == 0 {
                    lean_ctor_set(v___x_4360_, 0, v___x_4362_);
                    v___x_4364_ = v___x_4360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4362_);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_scopedEntries_4357_);
                    lean_ctor_set(v_reuseFailAlloc_4365_, 2, v_newEntries_4358_);
                    v___x_4364_ = v_reuseFailAlloc_4365_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addLocalEntry___redArg(
    mut v_ext_4367_: *mut LeanObject,
    mut v_env_4368_: *mut LeanObject,
    mut v_b_4369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4370_ = lean_ctor_get(v_ext_4367_, 1);
    lean_inc_ref(v_ext_4370_);
    v___f_4371_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_addLocalEntry___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4371_, 0, v_ext_4367_);
    lean_closure_set(v___f_4371_, 1, v_b_4369_);
    v___x_4372_ = lean_box(1);
    v___x_4373_ = lean_box(0);
    v___x_4374_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4370_,
        v_env_4368_,
        v___f_4371_,
        v___x_4372_,
        v___x_4373_,
    );
    return v___x_4374_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addLocalEntry(
    mut v_00_u03b1_4375_: *mut LeanObject,
    mut v_00_u03b2_4376_: *mut LeanObject,
    mut v_00_u03c3_4377_: *mut LeanObject,
    mut v_ext_4378_: *mut LeanObject,
    mut v_env_4379_: *mut LeanObject,
    mut v_b_4380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    v___x_4381_ =
        l_Lean_ScopedEnvExtension_addLocalEntry___redArg(v_ext_4378_, v_env_4379_, v_b_4380_);
    return v___x_4381_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore___redArg(
    mut v_env_4382_: *mut LeanObject,
    mut v_ext_4383_: *mut LeanObject,
    mut v_b_4384_: *mut LeanObject,
    mut v_kind_4385_: u8,
    mut v_namespaceName_4386_: *mut LeanObject,
) -> *mut LeanObject {
    match v_kind_4385_ {
        0 => {
            let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_namespaceName_4386_);
            v___x_4387_ =
                l_Lean_ScopedEnvExtension_addEntry___redArg(v_ext_4383_, v_env_4382_, v_b_4384_);
            return v___x_4387_;
        }
        1 => {
            let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_namespaceName_4386_);
            v___x_4388_ = l_Lean_ScopedEnvExtension_addLocalEntry___redArg(
                v_ext_4383_,
                v_env_4382_,
                v_b_4384_,
            );
            return v___x_4388_;
        }
        _ => {
            let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
            v___x_4389_ = l_Lean_ScopedEnvExtension_addScopedEntry___redArg(
                v_ext_4383_,
                v_env_4382_,
                v_namespaceName_4386_,
                v_b_4384_,
            );
            return v___x_4389_;
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore___redArg___boxed(
    mut v_env_4390_: *mut LeanObject,
    mut v_ext_4391_: *mut LeanObject,
    mut v_b_4392_: *mut LeanObject,
    mut v_kind_4393_: *mut LeanObject,
    mut v_namespaceName_4394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4395_: u8 = 0;
    let mut v_res_4396_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4395_ = (lean_unbox(v_kind_4393_) as u8);
    v_res_4396_ = l_Lean_ScopedEnvExtension_addCore___redArg(
        v_env_4390_,
        v_ext_4391_,
        v_b_4392_,
        v_kind_boxed_4395_,
        v_namespaceName_4394_,
    );
    return v_res_4396_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore(
    mut v_00_u03b1_4397_: *mut LeanObject,
    mut v_00_u03b2_4398_: *mut LeanObject,
    mut v_00_u03c3_4399_: *mut LeanObject,
    mut v_env_4400_: *mut LeanObject,
    mut v_ext_4401_: *mut LeanObject,
    mut v_b_4402_: *mut LeanObject,
    mut v_kind_4403_: u8,
    mut v_namespaceName_4404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    v___x_4405_ = l_Lean_ScopedEnvExtension_addCore___redArg(
        v_env_4400_,
        v_ext_4401_,
        v_b_4402_,
        v_kind_4403_,
        v_namespaceName_4404_,
    );
    return v___x_4405_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_addCore___boxed(
    mut v_00_u03b1_4406_: *mut LeanObject,
    mut v_00_u03b2_4407_: *mut LeanObject,
    mut v_00_u03c3_4408_: *mut LeanObject,
    mut v_env_4409_: *mut LeanObject,
    mut v_ext_4410_: *mut LeanObject,
    mut v_b_4411_: *mut LeanObject,
    mut v_kind_4412_: *mut LeanObject,
    mut v_namespaceName_4413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4414_: u8 = 0;
    let mut v_res_4415_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4414_ = (lean_unbox(v_kind_4412_) as u8);
    v_res_4415_ = l_Lean_ScopedEnvExtension_addCore(
        v_00_u03b1_4406_,
        v_00_u03b2_4407_,
        v_00_u03c3_4408_,
        v_env_4409_,
        v_ext_4410_,
        v_b_4411_,
        v_kind_boxed_4414_,
        v_namespaceName_4413_,
    );
    return v_res_4415_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__0(
    mut v_ext_4416_: *mut LeanObject,
    mut v_b_4417_: *mut LeanObject,
    mut v_kind_4418_: u8,
    mut v_ns_4419_: *mut LeanObject,
    mut v_x_4420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    v___x_4421_ = l_Lean_ScopedEnvExtension_addCore___redArg(
        v_x_4420_,
        v_ext_4416_,
        v_b_4417_,
        v_kind_4418_,
        v_ns_4419_,
    );
    return v___x_4421_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed(
    mut v_ext_4422_: *mut LeanObject,
    mut v_b_4423_: *mut LeanObject,
    mut v_kind_4424_: *mut LeanObject,
    mut v_ns_4425_: *mut LeanObject,
    mut v_x_4426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4427_: u8 = 0;
    let mut v_res_4428_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4427_ = (lean_unbox(v_kind_4424_) as u8);
    v_res_4428_ = l_Lean_ScopedEnvExtension_add___redArg___lam__0(
        v_ext_4422_,
        v_b_4423_,
        v_kind_boxed_4427_,
        v_ns_4425_,
        v_x_4426_,
    );
    return v_res_4428_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__1(
    mut v_inst_4429_: *mut LeanObject,
    mut v_ext_4430_: *mut LeanObject,
    mut v_b_4431_: *mut LeanObject,
    mut v_kind_4432_: u8,
    mut v_ns_4433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_4434_ = lean_ctor_get(v_inst_4429_, 1);
    lean_inc(v_modifyEnv_4434_);
    lean_dec_ref(v_inst_4429_);
    v___x_4435_ = lean_box((v_kind_4432_) as usize);
    v___f_4436_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_add___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4436_, 0, v_ext_4430_);
    lean_closure_set(v___f_4436_, 1, v_b_4431_);
    lean_closure_set(v___f_4436_, 2, v___x_4435_);
    lean_closure_set(v___f_4436_, 3, v_ns_4433_);
    v___x_4437_ = lean_apply_1(v_modifyEnv_4434_, v___f_4436_);
    return v___x_4437_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed(
    mut v_inst_4438_: *mut LeanObject,
    mut v_ext_4439_: *mut LeanObject,
    mut v_b_4440_: *mut LeanObject,
    mut v_kind_4441_: *mut LeanObject,
    mut v_ns_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4443_: u8 = 0;
    let mut v_res_4444_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4443_ = (lean_unbox(v_kind_4441_) as u8);
    v_res_4444_ = l_Lean_ScopedEnvExtension_add___redArg___lam__1(
        v_inst_4438_,
        v_ext_4439_,
        v_b_4440_,
        v_kind_boxed_4443_,
        v_ns_4442_,
    );
    return v_res_4444_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg(
    mut v_inst_4445_: *mut LeanObject,
    mut v_inst_4446_: *mut LeanObject,
    mut v_inst_4447_: *mut LeanObject,
    mut v_ext_4448_: *mut LeanObject,
    mut v_b_4449_: *mut LeanObject,
    mut v_kind_4450_: u8,
) -> *mut LeanObject {
    let mut v_toBind_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCurrNamespace_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_4451_ = lean_ctor_get(v_inst_4445_, 1);
    lean_inc(v_toBind_4451_);
    lean_dec_ref(v_inst_4445_);
    v_getCurrNamespace_4452_ = lean_ctor_get(v_inst_4446_, 0);
    lean_inc(v_getCurrNamespace_4452_);
    lean_dec_ref(v_inst_4446_);
    v___x_4453_ = lean_box((v_kind_4450_) as usize);
    v___f_4454_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_add___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_4454_, 0, v_inst_4447_);
    lean_closure_set(v___f_4454_, 1, v_ext_4448_);
    lean_closure_set(v___f_4454_, 2, v_b_4449_);
    lean_closure_set(v___f_4454_, 3, v___x_4453_);
    v___x_4455_ = lean_apply_4(
        v_toBind_4451_,
        lean_box(0),
        lean_box(0),
        v_getCurrNamespace_4452_,
        v___f_4454_,
    );
    return v___x_4455_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___redArg___boxed(
    mut v_inst_4456_: *mut LeanObject,
    mut v_inst_4457_: *mut LeanObject,
    mut v_inst_4458_: *mut LeanObject,
    mut v_ext_4459_: *mut LeanObject,
    mut v_b_4460_: *mut LeanObject,
    mut v_kind_4461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4462_: u8 = 0;
    let mut v_res_4463_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4462_ = (lean_unbox(v_kind_4461_) as u8);
    v_res_4463_ = l_Lean_ScopedEnvExtension_add___redArg(
        v_inst_4456_,
        v_inst_4457_,
        v_inst_4458_,
        v_ext_4459_,
        v_b_4460_,
        v_kind_boxed_4462_,
    );
    return v_res_4463_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add(
    mut v_m_4464_: *mut LeanObject,
    mut v_00_u03b1_4465_: *mut LeanObject,
    mut v_00_u03b2_4466_: *mut LeanObject,
    mut v_00_u03c3_4467_: *mut LeanObject,
    mut v_inst_4468_: *mut LeanObject,
    mut v_inst_4469_: *mut LeanObject,
    mut v_inst_4470_: *mut LeanObject,
    mut v_ext_4471_: *mut LeanObject,
    mut v_b_4472_: *mut LeanObject,
    mut v_kind_4473_: u8,
) -> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_ScopedEnvExtension_add___redArg(
        v_inst_4468_,
        v_inst_4469_,
        v_inst_4470_,
        v_ext_4471_,
        v_b_4472_,
        v_kind_4473_,
    );
    return v___x_4474_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___boxed(
    mut v_m_4475_: *mut LeanObject,
    mut v_00_u03b1_4476_: *mut LeanObject,
    mut v_00_u03b2_4477_: *mut LeanObject,
    mut v_00_u03c3_4478_: *mut LeanObject,
    mut v_inst_4479_: *mut LeanObject,
    mut v_inst_4480_: *mut LeanObject,
    mut v_inst_4481_: *mut LeanObject,
    mut v_ext_4482_: *mut LeanObject,
    mut v_b_4483_: *mut LeanObject,
    mut v_kind_4484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4485_: u8 = 0;
    let mut v_res_4486_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4485_ = (lean_unbox(v_kind_4484_) as u8);
    v_res_4486_ = l_Lean_ScopedEnvExtension_add(
        v_m_4475_,
        v_00_u03b1_4476_,
        v_00_u03b2_4477_,
        v_00_u03c3_4478_,
        v_inst_4479_,
        v_inst_4480_,
        v_inst_4481_,
        v_ext_4482_,
        v_b_4483_,
        v_kind_boxed_4485_,
    );
    return v_res_4486_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    v___x_4490_ = l_Lean_ScopedEnvExtension_getState___redArg___closed__2;
    v___x_4491_ = lean_unsigned_to_nat(16);
    v___x_4492_ = lean_unsigned_to_nat(209);
    v___x_4493_ = l_Lean_ScopedEnvExtension_getState___redArg___closed__1;
    v___x_4494_ = l_Lean_ScopedEnvExtension_getState___redArg___closed__0;
    v___x_4495_ = l_mkPanicMessageWithDecl(
        v___x_4494_,
        v___x_4493_,
        v___x_4492_,
        v___x_4491_,
        v___x_4490_,
    );
    return v___x_4495_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState___redArg(
    mut v_inst_4496_: *mut LeanObject,
    mut v_ext_4497_: *mut LeanObject,
    mut v_env_4498_: *mut LeanObject,
    mut v_asyncMode_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stateStack_4504_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4500_ = lean_ctor_get(v_ext_4497_, 1);
    v___x_4501_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0_once),
        _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__0,
    );
    v___x_4502_ = lean_box(0);
    v___x_4503_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_4501_,
        v_ext_4500_,
        v_env_4498_,
        v_asyncMode_4499_,
        v___x_4502_,
    );
    v_stateStack_4504_ = lean_ctor_get(v___x_4503_, 0);
    lean_inc(v_stateStack_4504_);
    lean_dec(v___x_4503_);
    if lean_obj_tag(v_stateStack_4504_) == 1 {
        let mut v_head_4505_: *mut LeanObject = core::ptr::null_mut();
        let mut v_state_4506_: *mut LeanObject = core::ptr::null_mut();
        v_head_4505_ = lean_ctor_get(v_stateStack_4504_, 0);
        lean_inc(v_head_4505_);
        lean_dec_ref_known(v_stateStack_4504_, 2);
        v_state_4506_ = lean_ctor_get(v_head_4505_, 0);
        lean_inc(v_state_4506_);
        lean_dec(v_head_4505_);
        return v_state_4506_;
    } else {
        let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stateStack_4504_);
        v___x_4507_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_getState___redArg___closed__3),
            core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_getState___redArg___closed__3_once),
            _init_l_Lean_ScopedEnvExtension_getState___redArg___closed__3,
        );
        v___x_4508_ = l_panic___redArg(v_inst_4496_, v___x_4507_);
        return v___x_4508_;
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState___redArg___boxed(
    mut v_inst_4509_: *mut LeanObject,
    mut v_ext_4510_: *mut LeanObject,
    mut v_env_4511_: *mut LeanObject,
    mut v_asyncMode_4512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4513_: *mut LeanObject = core::ptr::null_mut();
    v_res_4513_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v_inst_4509_,
        v_ext_4510_,
        v_env_4511_,
        v_asyncMode_4512_,
    );
    lean_dec(v_asyncMode_4512_);
    lean_dec_ref(v_ext_4510_);
    lean_dec(v_inst_4509_);
    return v_res_4513_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState(
    mut v_00_u03c3_4514_: *mut LeanObject,
    mut v_00_u03b1_4515_: *mut LeanObject,
    mut v_00_u03b2_4516_: *mut LeanObject,
    mut v_inst_4517_: *mut LeanObject,
    mut v_ext_4518_: *mut LeanObject,
    mut v_env_4519_: *mut LeanObject,
    mut v_asyncMode_4520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    v___x_4521_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v_inst_4517_,
        v_ext_4518_,
        v_env_4519_,
        v_asyncMode_4520_,
    );
    return v___x_4521_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_getState___boxed(
    mut v_00_u03c3_4522_: *mut LeanObject,
    mut v_00_u03b1_4523_: *mut LeanObject,
    mut v_00_u03b2_4524_: *mut LeanObject,
    mut v_inst_4525_: *mut LeanObject,
    mut v_ext_4526_: *mut LeanObject,
    mut v_env_4527_: *mut LeanObject,
    mut v_asyncMode_4528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4529_: *mut LeanObject = core::ptr::null_mut();
    v_res_4529_ = l_Lean_ScopedEnvExtension_getState(
        v_00_u03c3_4522_,
        v_00_u03b1_4523_,
        v_00_u03b2_4524_,
        v_inst_4525_,
        v_ext_4526_,
        v_env_4527_,
        v_asyncMode_4528_,
    );
    lean_dec(v_asyncMode_4528_);
    lean_dec_ref(v_ext_4526_);
    lean_dec(v_inst_4525_);
    return v_res_4529_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_ext_4530_: *mut LeanObject,
    mut v_as_4531_: *mut LeanObject,
    mut v_sz_4532_: usize,
    mut v_i_4533_: usize,
    mut v_b_4534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4535_: u8 = 0;
    let mut v_descr_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4540_: u8 = 0;
    let mut v_addEntry_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: usize = 0;
    let mut v___x_4548_: usize = 0;
    let mut v_reuseFailAlloc_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut v_unused_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4535_ = lean_usize_dec_lt(v_i_4533_, v_sz_4532_);
                if v___x_4535_ == 0 {
                    lean_dec_ref(v_ext_4530_);
                    return v_b_4534_;
                } else {
                    v_descr_4536_ = lean_ctor_get(v_ext_4530_, 0);
                    v_snd_4537_ = lean_ctor_get(v_b_4534_, 1);
                    v_isSharedCheck_4551_ = (!lean_is_exclusive(v_b_4534_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v_unused_4552_ = lean_ctor_get(v_b_4534_, 0);
                        lean_dec(v_unused_4552_);
                        v___x_4539_ = v_b_4534_;
                        v_isShared_4540_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4537_);
                        lean_dec(v_b_4534_);
                        v___x_4539_ = lean_box(0);
                        v_isShared_4540_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4541_ = lean_ctor_get(v_descr_4536_, 4);
                v___x_4542_ = lean_box(0);
                v_a_4543_ = lean_array_uget_borrowed(v_as_4531_, v_i_4533_);
                lean_inc(v_addEntry_4541_);
                lean_inc(v_a_4543_);
                v_state_4544_ = lean_apply_2(v_addEntry_4541_, v_snd_4537_, v_a_4543_);
                if v_isShared_4540_ == 0 {
                    lean_ctor_set(v___x_4539_, 1, v_state_4544_);
                    lean_ctor_set(v___x_4539_, 0, v___x_4542_);
                    v___x_4546_ = v___x_4539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4542_);
                    lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_state_4544_);
                    v___x_4546_ = v_reuseFailAlloc_4550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4547_ = 1usize;
                v___x_4548_ = lean_usize_add(v_i_4533_, v___x_4547_);
                v_i_4533_ = v___x_4548_;
                v_b_4534_ = v___x_4546_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_ext_4553_: *mut LeanObject,
    mut v_as_4554_: *mut LeanObject,
    mut v_sz_4555_: *mut LeanObject,
    mut v_i_4556_: *mut LeanObject,
    mut v_b_4557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4558_: usize = 0;
    let mut v_i_boxed_4559_: usize = 0;
    let mut v_res_4560_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4558_ = lean_unbox_usize(v_sz_4555_);
    lean_dec(v_sz_4555_);
    v_i_boxed_4559_ = lean_unbox_usize(v_i_4556_);
    lean_dec(v_i_4556_);
    v_res_4560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_4553_, v_as_4554_, v_sz_boxed_4558_, v_i_boxed_4559_, v_b_4557_);
    lean_dec_ref(v_as_4554_);
    return v_res_4560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(
    mut v_ext_4561_: *mut LeanObject,
    mut v_as_4562_: *mut LeanObject,
    mut v_sz_4563_: usize,
    mut v_i_4564_: usize,
    mut v_b_4565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4566_: u8 = 0;
    let mut v_descr_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v_addEntry_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: usize = 0;
    let mut v___x_4579_: usize = 0;
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4582_: u8 = 0;
    let mut v_unused_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4566_ = lean_usize_dec_lt(v_i_4564_, v_sz_4563_);
                if v___x_4566_ == 0 {
                    lean_dec_ref(v_ext_4561_);
                    return v_b_4565_;
                } else {
                    v_descr_4567_ = lean_ctor_get(v_ext_4561_, 0);
                    v_snd_4568_ = lean_ctor_get(v_b_4565_, 1);
                    v_isSharedCheck_4582_ = (!lean_is_exclusive(v_b_4565_)) as u8;
                    if v_isSharedCheck_4582_ == 0 {
                        v_unused_4583_ = lean_ctor_get(v_b_4565_, 0);
                        lean_dec(v_unused_4583_);
                        v___x_4570_ = v_b_4565_;
                        v_isShared_4571_ = v_isSharedCheck_4582_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4568_);
                        lean_dec(v_b_4565_);
                        v___x_4570_ = lean_box(0);
                        v_isShared_4571_ = v_isSharedCheck_4582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4572_ = lean_ctor_get(v_descr_4567_, 4);
                v___x_4573_ = lean_box(0);
                v_a_4574_ = lean_array_uget_borrowed(v_as_4562_, v_i_4564_);
                lean_inc(v_addEntry_4572_);
                lean_inc(v_a_4574_);
                v_state_4575_ = lean_apply_2(v_addEntry_4572_, v_snd_4568_, v_a_4574_);
                if v_isShared_4571_ == 0 {
                    lean_ctor_set(v___x_4570_, 1, v_state_4575_);
                    lean_ctor_set(v___x_4570_, 0, v___x_4573_);
                    v___x_4577_ = v___x_4570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4573_);
                    lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_state_4575_);
                    v___x_4577_ = v_reuseFailAlloc_4581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4578_ = 1usize;
                v___x_4579_ = lean_usize_add(v_i_4564_, v___x_4578_);
                v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_4561_, v_as_4562_, v_sz_4563_, v___x_4579_, v___x_4577_);
                return v___x_4580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ext_4584_: *mut LeanObject,
    mut v_as_4585_: *mut LeanObject,
    mut v_sz_4586_: *mut LeanObject,
    mut v_i_4587_: *mut LeanObject,
    mut v_b_4588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4589_: usize = 0;
    let mut v_i_boxed_4590_: usize = 0;
    let mut v_res_4591_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4589_ = lean_unbox_usize(v_sz_4586_);
    lean_dec(v_sz_4586_);
    v_i_boxed_4590_ = lean_unbox_usize(v_i_4587_);
    lean_dec(v_i_4587_);
    v_res_4591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_4584_, v_as_4585_, v_sz_boxed_4589_, v_i_boxed_4590_, v_b_4588_);
    lean_dec_ref(v_as_4585_);
    return v_res_4591_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(
    mut v_init_4592_: *mut LeanObject,
    mut v_ext_4593_: *mut LeanObject,
    mut v_n_4594_: *mut LeanObject,
    mut v_b_4595_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_n_4594_) == 0 {
        let mut v_cs_4596_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4599_: usize = 0;
        let mut v___x_4600_: usize = 0;
        let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4602_: *mut LeanObject = core::ptr::null_mut();
        v_cs_4596_ = lean_ctor_get(v_n_4594_, 0);
        v___x_4597_ = lean_box(0);
        v___x_4598_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4598_, 0, v___x_4597_);
        lean_ctor_set(v___x_4598_, 1, v_b_4595_);
        v_sz_4599_ = lean_array_size(v_cs_4596_);
        v___x_4600_ = 0usize;
        v___x_4601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_4592_, v_ext_4593_, v_cs_4596_, v_sz_4599_, v___x_4600_, v___x_4598_);
        v_fst_4602_ = lean_ctor_get(v___x_4601_, 0);
        lean_inc(v_fst_4602_);
        if lean_obj_tag(v_fst_4602_) == 0 {
            let mut v_snd_4603_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
            v_snd_4603_ = lean_ctor_get(v___x_4601_, 1);
            lean_inc(v_snd_4603_);
            lean_dec_ref(v___x_4601_);
            v___x_4604_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4604_, 0, v_snd_4603_);
            return v___x_4604_;
        } else {
            let mut v_val_4605_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_4601_);
            v_val_4605_ = lean_ctor_get(v_fst_4602_, 0);
            lean_inc(v_val_4605_);
            lean_dec_ref_known(v_fst_4602_, 1);
            return v_val_4605_;
        }
    } else {
        let mut v_vs_4606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4609_: usize = 0;
        let mut v___x_4610_: usize = 0;
        let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4612_: *mut LeanObject = core::ptr::null_mut();
        v_vs_4606_ = lean_ctor_get(v_n_4594_, 0);
        v___x_4607_ = lean_box(0);
        v___x_4608_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4608_, 0, v___x_4607_);
        lean_ctor_set(v___x_4608_, 1, v_b_4595_);
        v_sz_4609_ = lean_array_size(v_vs_4606_);
        v___x_4610_ = 0usize;
        v___x_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_4593_, v_vs_4606_, v_sz_4609_, v___x_4610_, v___x_4608_);
        v_fst_4612_ = lean_ctor_get(v___x_4611_, 0);
        lean_inc(v_fst_4612_);
        if lean_obj_tag(v_fst_4612_) == 0 {
            let mut v_snd_4613_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
            v_snd_4613_ = lean_ctor_get(v___x_4611_, 1);
            lean_inc(v_snd_4613_);
            lean_dec_ref(v___x_4611_);
            v___x_4614_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4614_, 0, v_snd_4613_);
            return v___x_4614_;
        } else {
            let mut v_val_4615_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_4611_);
            v_val_4615_ = lean_ctor_get(v_fst_4612_, 0);
            lean_inc(v_val_4615_);
            lean_dec_ref_known(v_fst_4612_, 1);
            return v_val_4615_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(
    mut v_init_4616_: *mut LeanObject,
    mut v_ext_4617_: *mut LeanObject,
    mut v_as_4618_: *mut LeanObject,
    mut v_sz_4619_: usize,
    mut v_i_4620_: usize,
    mut v_b_4621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4622_: u8 = 0;
    let mut v_snd_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v_a_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: usize = 0;
    let mut v___x_4638_: usize = 0;
    let mut v_reuseFailAlloc_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4641_: u8 = 0;
    let mut v_unused_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4622_ = lean_usize_dec_lt(v_i_4620_, v_sz_4619_);
                if v___x_4622_ == 0 {
                    lean_dec_ref(v_ext_4617_);
                    return v_b_4621_;
                } else {
                    v_snd_4623_ = lean_ctor_get(v_b_4621_, 1);
                    v_isSharedCheck_4641_ = (!lean_is_exclusive(v_b_4621_)) as u8;
                    if v_isSharedCheck_4641_ == 0 {
                        v_unused_4642_ = lean_ctor_get(v_b_4621_, 0);
                        lean_dec(v_unused_4642_);
                        v___x_4625_ = v_b_4621_;
                        v_isShared_4626_ = v_isSharedCheck_4641_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4623_);
                        lean_dec(v_b_4621_);
                        v___x_4625_ = lean_box(0);
                        v_isShared_4626_ = v_isSharedCheck_4641_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4627_ = lean_array_uget_borrowed(v_as_4618_, v_i_4620_);
                lean_inc(v_snd_4623_);
                lean_inc_ref(v_ext_4617_);
                v___x_4628_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4616_, v_ext_4617_, v_a_4627_, v_snd_4623_);
                if lean_obj_tag(v___x_4628_) == 0 {
                    lean_dec_ref(v_ext_4617_);
                    v___x_4629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4629_, 0, v___x_4628_);
                    if v_isShared_4626_ == 0 {
                        lean_ctor_set(v___x_4625_, 0, v___x_4629_);
                        v___x_4631_ = v___x_4625_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4629_);
                        lean_ctor_set(v_reuseFailAlloc_4632_, 1, v_snd_4623_);
                        v___x_4631_ = v_reuseFailAlloc_4632_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_4623_);
                    v_a_4633_ = lean_ctor_get(v___x_4628_, 0);
                    lean_inc(v_a_4633_);
                    lean_dec_ref_known(v___x_4628_, 1);
                    v___x_4634_ = lean_box(0);
                    if v_isShared_4626_ == 0 {
                        lean_ctor_set(v___x_4625_, 1, v_a_4633_);
                        lean_ctor_set(v___x_4625_, 0, v___x_4634_);
                        v___x_4636_ = v___x_4625_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4634_);
                        lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_a_4633_);
                        v___x_4636_ = v_reuseFailAlloc_4640_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4631_;
            }
            3 => {
                v___x_4637_ = 1usize;
                v___x_4638_ = lean_usize_add(v_i_4620_, v___x_4637_);
                v_i_4620_ = v___x_4638_;
                v_b_4621_ = v___x_4636_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_init_4643_: *mut LeanObject,
    mut v_ext_4644_: *mut LeanObject,
    mut v_as_4645_: *mut LeanObject,
    mut v_sz_4646_: *mut LeanObject,
    mut v_i_4647_: *mut LeanObject,
    mut v_b_4648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4649_: usize = 0;
    let mut v_i_boxed_4650_: usize = 0;
    let mut v_res_4651_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4649_ = lean_unbox_usize(v_sz_4646_);
    lean_dec(v_sz_4646_);
    v_i_boxed_4650_ = lean_unbox_usize(v_i_4647_);
    lean_dec(v_i_4647_);
    v_res_4651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_4643_, v_ext_4644_, v_as_4645_, v_sz_boxed_4649_, v_i_boxed_4650_, v_b_4648_);
    lean_dec_ref(v_as_4645_);
    lean_dec(v_init_4643_);
    return v_res_4651_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg___boxed(
    mut v_init_4652_: *mut LeanObject,
    mut v_ext_4653_: *mut LeanObject,
    mut v_n_4654_: *mut LeanObject,
    mut v_b_4655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4656_: *mut LeanObject = core::ptr::null_mut();
    v_res_4656_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4652_, v_ext_4653_, v_n_4654_, v_b_4655_);
    lean_dec_ref(v_n_4654_);
    lean_dec(v_init_4652_);
    return v_res_4656_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(
    mut v_ext_4657_: *mut LeanObject,
    mut v_as_4658_: *mut LeanObject,
    mut v_sz_4659_: usize,
    mut v_i_4660_: usize,
    mut v_b_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4662_: u8 = 0;
    let mut v_descr_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4667_: u8 = 0;
    let mut v_addEntry_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: usize = 0;
    let mut v___x_4675_: usize = 0;
    let mut v_reuseFailAlloc_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v_unused_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4662_ = lean_usize_dec_lt(v_i_4660_, v_sz_4659_);
                if v___x_4662_ == 0 {
                    lean_dec_ref(v_ext_4657_);
                    return v_b_4661_;
                } else {
                    v_descr_4663_ = lean_ctor_get(v_ext_4657_, 0);
                    v_snd_4664_ = lean_ctor_get(v_b_4661_, 1);
                    v_isSharedCheck_4678_ = (!lean_is_exclusive(v_b_4661_)) as u8;
                    if v_isSharedCheck_4678_ == 0 {
                        v_unused_4679_ = lean_ctor_get(v_b_4661_, 0);
                        lean_dec(v_unused_4679_);
                        v___x_4666_ = v_b_4661_;
                        v_isShared_4667_ = v_isSharedCheck_4678_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4664_);
                        lean_dec(v_b_4661_);
                        v___x_4666_ = lean_box(0);
                        v_isShared_4667_ = v_isSharedCheck_4678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4668_ = lean_ctor_get(v_descr_4663_, 4);
                v___x_4669_ = lean_box(0);
                v_a_4670_ = lean_array_uget_borrowed(v_as_4658_, v_i_4660_);
                lean_inc(v_addEntry_4668_);
                lean_inc(v_a_4670_);
                v_state_4671_ = lean_apply_2(v_addEntry_4668_, v_snd_4664_, v_a_4670_);
                if v_isShared_4667_ == 0 {
                    lean_ctor_set(v___x_4666_, 1, v_state_4671_);
                    lean_ctor_set(v___x_4666_, 0, v___x_4669_);
                    v___x_4673_ = v___x_4666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4669_);
                    lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_state_4671_);
                    v___x_4673_ = v_reuseFailAlloc_4677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4674_ = 1usize;
                v___x_4675_ = lean_usize_add(v_i_4660_, v___x_4674_);
                v_i_4660_ = v___x_4675_;
                v_b_4661_ = v___x_4673_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ext_4680_: *mut LeanObject,
    mut v_as_4681_: *mut LeanObject,
    mut v_sz_4682_: *mut LeanObject,
    mut v_i_4683_: *mut LeanObject,
    mut v_b_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4685_: usize = 0;
    let mut v_i_boxed_4686_: usize = 0;
    let mut v_res_4687_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4685_ = lean_unbox_usize(v_sz_4682_);
    lean_dec(v_sz_4682_);
    v_i_boxed_4686_ = lean_unbox_usize(v_i_4683_);
    lean_dec(v_i_4683_);
    v_res_4687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_4680_, v_as_4681_, v_sz_boxed_4685_, v_i_boxed_4686_, v_b_4684_);
    lean_dec_ref(v_as_4681_);
    return v_res_4687_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(
    mut v_ext_4688_: *mut LeanObject,
    mut v_as_4689_: *mut LeanObject,
    mut v_sz_4690_: usize,
    mut v_i_4691_: usize,
    mut v_b_4692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4693_: u8 = 0;
    let mut v_descr_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v_addEntry_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: usize = 0;
    let mut v___x_4706_: usize = 0;
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4709_: u8 = 0;
    let mut v_unused_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4693_ = lean_usize_dec_lt(v_i_4691_, v_sz_4690_);
                if v___x_4693_ == 0 {
                    lean_dec_ref(v_ext_4688_);
                    return v_b_4692_;
                } else {
                    v_descr_4694_ = lean_ctor_get(v_ext_4688_, 0);
                    v_snd_4695_ = lean_ctor_get(v_b_4692_, 1);
                    v_isSharedCheck_4709_ = (!lean_is_exclusive(v_b_4692_)) as u8;
                    if v_isSharedCheck_4709_ == 0 {
                        v_unused_4710_ = lean_ctor_get(v_b_4692_, 0);
                        lean_dec(v_unused_4710_);
                        v___x_4697_ = v_b_4692_;
                        v_isShared_4698_ = v_isSharedCheck_4709_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4695_);
                        lean_dec(v_b_4692_);
                        v___x_4697_ = lean_box(0);
                        v_isShared_4698_ = v_isSharedCheck_4709_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_addEntry_4699_ = lean_ctor_get(v_descr_4694_, 4);
                v___x_4700_ = lean_box(0);
                v_a_4701_ = lean_array_uget_borrowed(v_as_4689_, v_i_4691_);
                lean_inc(v_addEntry_4699_);
                lean_inc(v_a_4701_);
                v_state_4702_ = lean_apply_2(v_addEntry_4699_, v_snd_4695_, v_a_4701_);
                if v_isShared_4698_ == 0 {
                    lean_ctor_set(v___x_4697_, 1, v_state_4702_);
                    lean_ctor_set(v___x_4697_, 0, v___x_4700_);
                    v___x_4704_ = v___x_4697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4700_);
                    lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_state_4702_);
                    v___x_4704_ = v_reuseFailAlloc_4708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4705_ = 1usize;
                v___x_4706_ = lean_usize_add(v_i_4691_, v___x_4705_);
                v___x_4707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_4688_, v_as_4689_, v_sz_4690_, v___x_4706_, v___x_4704_);
                return v___x_4707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg___boxed(
    mut v_ext_4711_: *mut LeanObject,
    mut v_as_4712_: *mut LeanObject,
    mut v_sz_4713_: *mut LeanObject,
    mut v_i_4714_: *mut LeanObject,
    mut v_b_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4716_: usize = 0;
    let mut v_i_boxed_4717_: usize = 0;
    let mut v_res_4718_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4716_ = lean_unbox_usize(v_sz_4713_);
    lean_dec(v_sz_4713_);
    v_i_boxed_4717_ = lean_unbox_usize(v_i_4714_);
    lean_dec(v_i_4714_);
    v_res_4718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_4711_, v_as_4712_, v_sz_boxed_4716_, v_i_boxed_4717_, v_b_4715_);
    lean_dec_ref(v_as_4712_);
    return v_res_4718_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(
    mut v_ext_4719_: *mut LeanObject,
    mut v_t_4720_: *mut LeanObject,
    mut v_init_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    v_root_4722_ = lean_ctor_get(v_t_4720_, 0);
    v_tail_4723_ = lean_ctor_get(v_t_4720_, 1);
    lean_inc_ref(v_ext_4719_);
    lean_inc(v_init_4721_);
    v___x_4724_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4721_, v_ext_4719_, v_root_4722_, v_init_4721_);
    lean_dec(v_init_4721_);
    if lean_obj_tag(v___x_4724_) == 0 {
        let mut v_a_4725_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ext_4719_);
        v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
        lean_inc(v_a_4725_);
        lean_dec_ref_known(v___x_4724_, 1);
        return v_a_4725_;
    } else {
        let mut v_a_4726_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_4729_: usize = 0;
        let mut v___x_4730_: usize = 0;
        let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_4732_: *mut LeanObject = core::ptr::null_mut();
        v_a_4726_ = lean_ctor_get(v___x_4724_, 0);
        lean_inc(v_a_4726_);
        lean_dec_ref_known(v___x_4724_, 1);
        v___x_4727_ = lean_box(0);
        v___x_4728_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4728_, 0, v___x_4727_);
        lean_ctor_set(v___x_4728_, 1, v_a_4726_);
        v_sz_4729_ = lean_array_size(v_tail_4723_);
        v___x_4730_ = 0usize;
        v___x_4731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_4719_, v_tail_4723_, v_sz_4729_, v___x_4730_, v___x_4728_);
        v_fst_4732_ = lean_ctor_get(v___x_4731_, 0);
        lean_inc(v_fst_4732_);
        if lean_obj_tag(v_fst_4732_) == 0 {
            let mut v_snd_4733_: *mut LeanObject = core::ptr::null_mut();
            v_snd_4733_ = lean_ctor_get(v___x_4731_, 1);
            lean_inc(v_snd_4733_);
            lean_dec_ref(v___x_4731_);
            return v_snd_4733_;
        } else {
            let mut v_val_4734_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_4731_);
            v_val_4734_ = lean_ctor_get(v_fst_4732_, 0);
            lean_inc(v_val_4734_);
            lean_dec_ref_known(v_fst_4732_, 1);
            return v_val_4734_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg___boxed(
    mut v_ext_4735_: *mut LeanObject,
    mut v_t_4736_: *mut LeanObject,
    mut v_init_4737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4738_: *mut LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_4735_, v_t_4736_, v_init_4737_);
    lean_dec_ref(v_t_4736_);
    return v_res_4738_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0(
    mut v_namespaceName_4739_: *mut LeanObject,
    mut v_ext_4740_: *mut LeanObject,
    mut v_s_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stateStack_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___y_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_state_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_4758_: u8 = 0;
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: u8 = 0;
    let mut v_activeScopes_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_isSharedCheck_4775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4742_ = lean_ctor_get(v_s_4741_, 0);
                lean_inc(v_stateStack_4742_);
                if lean_obj_tag(v_stateStack_4742_) == 1 {
                    v_scopedEntries_4743_ = lean_ctor_get(v_s_4741_, 1);
                    v_newEntries_4744_ = lean_ctor_get(v_s_4741_, 2);
                    v_head_4745_ = lean_ctor_get(v_stateStack_4742_, 0);
                    v_tail_4746_ = lean_ctor_get(v_stateStack_4742_, 1);
                    v_isSharedCheck_4775_ = (!lean_is_exclusive(v_stateStack_4742_)) as u8;
                    if v_isSharedCheck_4775_ == 0 {
                        v___x_4748_ = v_stateStack_4742_;
                        v_isShared_4749_ = v_isSharedCheck_4775_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4746_);
                        lean_inc(v_head_4745_);
                        lean_dec(v_stateStack_4742_);
                        v___x_4748_ = lean_box(0);
                        v_isShared_4749_ = v_isSharedCheck_4775_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_stateStack_4742_);
                    lean_dec_ref(v_ext_4740_);
                    lean_dec(v_namespaceName_4739_);
                    return v_s_4741_;
                }
            }
            1 => {
                v_state_4756_ = lean_ctor_get(v_head_4745_, 0);
                v_activeScopes_4757_ = lean_ctor_get(v_head_4745_, 1);
                v_delimitsLocal_4758_ = lean_ctor_get_uint8(
                    v_head_4745_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_4774_ = (!lean_is_exclusive(v_head_4745_)) as u8;
                if v_isSharedCheck_4774_ == 0 {
                    v___x_4760_ = v_head_4745_;
                    v_isShared_4761_ = v_isSharedCheck_4774_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_activeScopes_4757_);
                    lean_inc(v_state_4756_);
                    lean_dec(v_head_4745_);
                    v___x_4760_ = lean_box(0);
                    v_isShared_4761_ = v_isSharedCheck_4774_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                if v_isShared_4749_ == 0 {
                    lean_ctor_set(v___x_4748_, 0, v___y_4751_);
                    v___x_4753_ = v___x_4748_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___y_4751_);
                    lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_tail_4746_);
                    v___x_4753_ = v_reuseFailAlloc_4755_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4754_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4754_, 0, v___x_4753_);
                lean_ctor_set(v___x_4754_, 1, v_scopedEntries_4743_);
                lean_ctor_set(v___x_4754_, 2, v_newEntries_4744_);
                return v___x_4754_;
            }
            4 => {
                v___x_4762_ = l_Lean_NameSet_contains(v_activeScopes_4757_, v_namespaceName_4739_);
                if v___x_4762_ == 0 {
                    lean_inc(v_newEntries_4744_);
                    lean_inc_ref(v_scopedEntries_4743_);
                    lean_dec_ref(v_s_4741_);
                    lean_inc(v_namespaceName_4739_);
                    v_activeScopes_4763_ =
                        l_Lean_NameSet_insert(v_activeScopes_4757_, v_namespaceName_4739_);
                    v___x_4764_ = l_Lean_SMap_find_x3f___at___00Lean_ScopedEnvExtension_ScopedEntries_insert_spec__0___redArg(v_scopedEntries_4743_, v_namespaceName_4739_);
                    lean_dec(v_namespaceName_4739_);
                    if lean_obj_tag(v___x_4764_) == 0 {
                        lean_dec_ref(v_ext_4740_);
                        if v_isShared_4761_ == 0 {
                            lean_ctor_set(v___x_4760_, 1, v_activeScopes_4763_);
                            v___x_4766_ = v___x_4760_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_state_4756_);
                            lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_activeScopes_4763_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_4767_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v_delimitsLocal_4758_,
                            );
                            v___x_4766_ = v_reuseFailAlloc_4767_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_val_4768_ = lean_ctor_get(v___x_4764_, 0);
                        lean_inc(v_val_4768_);
                        lean_dec_ref_known(v___x_4764_, 1);
                        v___x_4769_ = 1;
                        v___x_4770_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_4740_, v_val_4768_, v_state_4756_);
                        lean_dec(v_val_4768_);
                        if v_isShared_4761_ == 0 {
                            lean_ctor_set(v___x_4760_, 1, v_activeScopes_4763_);
                            lean_ctor_set(v___x_4760_, 0, v___x_4770_);
                            v___x_4772_ = v___x_4760_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4770_);
                            lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_activeScopes_4763_);
                            v___x_4772_ = v_reuseFailAlloc_4773_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4760_);
                    lean_dec(v_activeScopes_4757_);
                    lean_dec(v_state_4756_);
                    lean_del_object(v___x_4748_);
                    lean_dec(v_tail_4746_);
                    lean_dec_ref(v_ext_4740_);
                    lean_dec(v_namespaceName_4739_);
                    return v_s_4741_;
                }
            }
            5 => {
                v___y_4751_ = v___x_4766_;
                state = 2;
                continue;
            }
            6 => {
                lean_ctor_set_uint8(
                    v___x_4772_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_4769_,
                );
                v___y_4751_ = v___x_4772_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_activateScoped___redArg(
    mut v_ext_4776_: *mut LeanObject,
    mut v_env_4777_: *mut LeanObject,
    mut v_namespaceName_4778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4779_ = lean_ctor_get(v_ext_4776_, 1);
    lean_inc_ref(v_ext_4779_);
    v___f_4780_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_activateScoped___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4780_, 0, v_namespaceName_4778_);
    lean_closure_set(v___f_4780_, 1, v_ext_4776_);
    v___x_4781_ = lean_box(1);
    v___x_4782_ = lean_box(0);
    v___x_4783_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4779_,
        v_env_4777_,
        v___f_4780_,
        v___x_4781_,
        v___x_4782_,
    );
    return v___x_4783_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_activateScoped(
    mut v_00_u03b1_4784_: *mut LeanObject,
    mut v_00_u03b2_4785_: *mut LeanObject,
    mut v_00_u03c3_4786_: *mut LeanObject,
    mut v_ext_4787_: *mut LeanObject,
    mut v_env_4788_: *mut LeanObject,
    mut v_namespaceName_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    v___x_4790_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(
        v_ext_4787_,
        v_env_4788_,
        v_namespaceName_4789_,
    );
    return v___x_4790_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(
    mut v_00_u03b2_4791_: *mut LeanObject,
    mut v_00_u03c3_4792_: *mut LeanObject,
    mut v_00_u03b1_4793_: *mut LeanObject,
    mut v_ext_4794_: *mut LeanObject,
    mut v_t_4795_: *mut LeanObject,
    mut v_init_4796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    v___x_4797_ = l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___redArg(v_ext_4794_, v_t_4795_, v_init_4796_);
    return v___x_4797_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0___boxed(
    mut v_00_u03b2_4798_: *mut LeanObject,
    mut v_00_u03c3_4799_: *mut LeanObject,
    mut v_00_u03b1_4800_: *mut LeanObject,
    mut v_ext_4801_: *mut LeanObject,
    mut v_t_4802_: *mut LeanObject,
    mut v_init_4803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4804_: *mut LeanObject = core::ptr::null_mut();
    v_res_4804_ =
        l_Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0(
            v_00_u03b2_4798_,
            v_00_u03c3_4799_,
            v_00_u03b1_4800_,
            v_ext_4801_,
            v_t_4802_,
            v_init_4803_,
        );
    lean_dec_ref(v_t_4802_);
    return v_res_4804_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(
    mut v_00_u03b2_4805_: *mut LeanObject,
    mut v_00_u03c3_4806_: *mut LeanObject,
    mut v_init_4807_: *mut LeanObject,
    mut v_00_u03b1_4808_: *mut LeanObject,
    mut v_ext_4809_: *mut LeanObject,
    mut v_n_4810_: *mut LeanObject,
    mut v_b_4811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    v___x_4812_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___redArg(v_init_4807_, v_ext_4809_, v_n_4810_, v_b_4811_);
    return v___x_4812_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0___boxed(
    mut v_00_u03b2_4813_: *mut LeanObject,
    mut v_00_u03c3_4814_: *mut LeanObject,
    mut v_init_4815_: *mut LeanObject,
    mut v_00_u03b1_4816_: *mut LeanObject,
    mut v_ext_4817_: *mut LeanObject,
    mut v_n_4818_: *mut LeanObject,
    mut v_b_4819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4820_: *mut LeanObject = core::ptr::null_mut();
    v_res_4820_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0(v_00_u03b2_4813_, v_00_u03c3_4814_, v_init_4815_, v_00_u03b1_4816_, v_ext_4817_, v_n_4818_, v_b_4819_);
    lean_dec_ref(v_n_4818_);
    lean_dec(v_init_4815_);
    return v_res_4820_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(
    mut v_00_u03b2_4821_: *mut LeanObject,
    mut v_00_u03c3_4822_: *mut LeanObject,
    mut v_00_u03b1_4823_: *mut LeanObject,
    mut v_ext_4824_: *mut LeanObject,
    mut v_as_4825_: *mut LeanObject,
    mut v_sz_4826_: usize,
    mut v_i_4827_: usize,
    mut v_b_4828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    v___x_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___redArg(v_ext_4824_, v_as_4825_, v_sz_4826_, v_i_4827_, v_b_4828_);
    return v___x_4829_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1___boxed(
    mut v_00_u03b2_4830_: *mut LeanObject,
    mut v_00_u03c3_4831_: *mut LeanObject,
    mut v_00_u03b1_4832_: *mut LeanObject,
    mut v_ext_4833_: *mut LeanObject,
    mut v_as_4834_: *mut LeanObject,
    mut v_sz_4835_: *mut LeanObject,
    mut v_i_4836_: *mut LeanObject,
    mut v_b_4837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4838_: usize = 0;
    let mut v_i_boxed_4839_: usize = 0;
    let mut v_res_4840_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4838_ = lean_unbox_usize(v_sz_4835_);
    lean_dec(v_sz_4835_);
    v_i_boxed_4839_ = lean_unbox_usize(v_i_4836_);
    lean_dec(v_i_4836_);
    v_res_4840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1(v_00_u03b2_4830_, v_00_u03c3_4831_, v_00_u03b1_4832_, v_ext_4833_, v_as_4834_, v_sz_boxed_4838_, v_i_boxed_4839_, v_b_4837_);
    lean_dec_ref(v_as_4834_);
    return v_res_4840_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4841_: *mut LeanObject,
    mut v_00_u03c3_4842_: *mut LeanObject,
    mut v_init_4843_: *mut LeanObject,
    mut v_00_u03b1_4844_: *mut LeanObject,
    mut v_ext_4845_: *mut LeanObject,
    mut v_as_4846_: *mut LeanObject,
    mut v_sz_4847_: usize,
    mut v_i_4848_: usize,
    mut v_b_4849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    v___x_4850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___redArg(v_init_4843_, v_ext_4845_, v_as_4846_, v_sz_4847_, v_i_4848_, v_b_4849_);
    return v___x_4850_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4851_: *mut LeanObject,
    mut v_00_u03c3_4852_: *mut LeanObject,
    mut v_init_4853_: *mut LeanObject,
    mut v_00_u03b1_4854_: *mut LeanObject,
    mut v_ext_4855_: *mut LeanObject,
    mut v_as_4856_: *mut LeanObject,
    mut v_sz_4857_: *mut LeanObject,
    mut v_i_4858_: *mut LeanObject,
    mut v_b_4859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4860_: usize = 0;
    let mut v_i_boxed_4861_: usize = 0;
    let mut v_res_4862_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4860_ = lean_unbox_usize(v_sz_4857_);
    lean_dec(v_sz_4857_);
    v_i_boxed_4861_ = lean_unbox_usize(v_i_4858_);
    lean_dec(v_i_4858_);
    v_res_4862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__1(v_00_u03b2_4851_, v_00_u03c3_4852_, v_init_4853_, v_00_u03b1_4854_, v_ext_4855_, v_as_4856_, v_sz_boxed_4860_, v_i_boxed_4861_, v_b_4859_);
    lean_dec_ref(v_as_4856_);
    lean_dec(v_init_4853_);
    return v_res_4862_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4863_: *mut LeanObject,
    mut v_00_u03c3_4864_: *mut LeanObject,
    mut v_00_u03b1_4865_: *mut LeanObject,
    mut v_ext_4866_: *mut LeanObject,
    mut v_as_4867_: *mut LeanObject,
    mut v_sz_4868_: usize,
    mut v_i_4869_: usize,
    mut v_b_4870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    v___x_4871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___redArg(v_ext_4866_, v_as_4867_, v_sz_4868_, v_i_4869_, v_b_4870_);
    return v___x_4871_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4872_: *mut LeanObject,
    mut v_00_u03c3_4873_: *mut LeanObject,
    mut v_00_u03b1_4874_: *mut LeanObject,
    mut v_ext_4875_: *mut LeanObject,
    mut v_as_4876_: *mut LeanObject,
    mut v_sz_4877_: *mut LeanObject,
    mut v_i_4878_: *mut LeanObject,
    mut v_b_4879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4880_: usize = 0;
    let mut v_i_boxed_4881_: usize = 0;
    let mut v_res_4882_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4880_ = lean_unbox_usize(v_sz_4877_);
    lean_dec(v_sz_4877_);
    v_i_boxed_4881_ = lean_unbox_usize(v_i_4878_);
    lean_dec(v_i_4878_);
    v_res_4882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2(v_00_u03b2_4872_, v_00_u03c3_4873_, v_00_u03b1_4874_, v_ext_4875_, v_as_4876_, v_sz_boxed_4880_, v_i_boxed_4881_, v_b_4879_);
    lean_dec_ref(v_as_4876_);
    return v_res_4882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4883_: *mut LeanObject,
    mut v_00_u03c3_4884_: *mut LeanObject,
    mut v_00_u03b1_4885_: *mut LeanObject,
    mut v_ext_4886_: *mut LeanObject,
    mut v_as_4887_: *mut LeanObject,
    mut v_sz_4888_: usize,
    mut v_i_4889_: usize,
    mut v_b_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v___x_4891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___redArg(v_ext_4886_, v_as_4887_, v_sz_4888_, v_i_4889_, v_b_4890_);
    return v___x_4891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_4892_: *mut LeanObject,
    mut v_00_u03c3_4893_: *mut LeanObject,
    mut v_00_u03b1_4894_: *mut LeanObject,
    mut v_ext_4895_: *mut LeanObject,
    mut v_as_4896_: *mut LeanObject,
    mut v_sz_4897_: *mut LeanObject,
    mut v_i_4898_: *mut LeanObject,
    mut v_b_4899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4900_: usize = 0;
    let mut v_i_boxed_4901_: usize = 0;
    let mut v_res_4902_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4900_ = lean_unbox_usize(v_sz_4897_);
    lean_dec(v_sz_4897_);
    v_i_boxed_4901_ = lean_unbox_usize(v_i_4898_);
    lean_dec(v_i_4898_);
    v_res_4902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__1_spec__4(v_00_u03b2_4892_, v_00_u03c3_4893_, v_00_u03b1_4894_, v_ext_4895_, v_as_4896_, v_sz_boxed_4900_, v_i_boxed_4901_, v_b_4899_);
    lean_dec_ref(v_as_4896_);
    return v_res_4902_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_4903_: *mut LeanObject,
    mut v_00_u03c3_4904_: *mut LeanObject,
    mut v_00_u03b1_4905_: *mut LeanObject,
    mut v_ext_4906_: *mut LeanObject,
    mut v_as_4907_: *mut LeanObject,
    mut v_sz_4908_: usize,
    mut v_i_4909_: usize,
    mut v_b_4910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    v___x_4911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___redArg(v_ext_4906_, v_as_4907_, v_sz_4908_, v_i_4909_, v_b_4910_);
    return v___x_4911_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_00_u03b2_4912_: *mut LeanObject,
    mut v_00_u03c3_4913_: *mut LeanObject,
    mut v_00_u03b1_4914_: *mut LeanObject,
    mut v_ext_4915_: *mut LeanObject,
    mut v_as_4916_: *mut LeanObject,
    mut v_sz_4917_: *mut LeanObject,
    mut v_i_4918_: *mut LeanObject,
    mut v_b_4919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4920_: usize = 0;
    let mut v_i_boxed_4921_: usize = 0;
    let mut v_res_4922_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4920_ = lean_unbox_usize(v_sz_4917_);
    lean_dec(v_sz_4917_);
    v_i_boxed_4921_ = lean_unbox_usize(v_i_4918_);
    lean_dec(v_i_4918_);
    v_res_4922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_ScopedEnvExtension_activateScoped_spec__0_spec__0_spec__2_spec__3(v_00_u03b2_4912_, v_00_u03c3_4913_, v_00_u03b1_4914_, v_ext_4915_, v_as_4916_, v_sz_boxed_4920_, v_i_boxed_4921_, v_b_4919_);
    lean_dec_ref(v_as_4916_);
    return v_res_4922_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0(
    mut v_f_4923_: *mut LeanObject,
    mut v_s_4924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stateStack_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopedEntries_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v_tail_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v_state_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeScopes_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_delimitsLocal_4938_: u8 = 0;
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4952_: u8 = 0;
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v_unused_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_unused_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stateStack_4925_ = lean_ctor_get(v_s_4924_, 0);
                lean_inc(v_stateStack_4925_);
                if lean_obj_tag(v_stateStack_4925_) == 1 {
                    v_head_4926_ = lean_ctor_get(v_stateStack_4925_, 0);
                    lean_inc(v_head_4926_);
                    v_scopedEntries_4927_ = lean_ctor_get(v_s_4924_, 1);
                    v_newEntries_4928_ = lean_ctor_get(v_s_4924_, 2);
                    v_isSharedCheck_4955_ = (!lean_is_exclusive(v_s_4924_)) as u8;
                    if v_isSharedCheck_4955_ == 0 {
                        v_unused_4956_ = lean_ctor_get(v_s_4924_, 0);
                        lean_dec(v_unused_4956_);
                        v___x_4930_ = v_s_4924_;
                        v_isShared_4931_ = v_isSharedCheck_4955_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_newEntries_4928_);
                        lean_inc(v_scopedEntries_4927_);
                        lean_dec(v_s_4924_);
                        v___x_4930_ = lean_box(0);
                        v_isShared_4931_ = v_isSharedCheck_4955_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_stateStack_4925_);
                    lean_dec(v_f_4923_);
                    return v_s_4924_;
                }
            }
            1 => {
                v_tail_4932_ = lean_ctor_get(v_stateStack_4925_, 1);
                v_isSharedCheck_4953_ = (!lean_is_exclusive(v_stateStack_4925_)) as u8;
                if v_isSharedCheck_4953_ == 0 {
                    v_unused_4954_ = lean_ctor_get(v_stateStack_4925_, 0);
                    lean_dec(v_unused_4954_);
                    v___x_4934_ = v_stateStack_4925_;
                    v_isShared_4935_ = v_isSharedCheck_4953_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_tail_4932_);
                    lean_dec(v_stateStack_4925_);
                    v___x_4934_ = lean_box(0);
                    v_isShared_4935_ = v_isSharedCheck_4953_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_state_4936_ = lean_ctor_get(v_head_4926_, 0);
                v_activeScopes_4937_ = lean_ctor_get(v_head_4926_, 1);
                v_delimitsLocal_4938_ = lean_ctor_get_uint8(
                    v_head_4926_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_4952_ = (!lean_is_exclusive(v_head_4926_)) as u8;
                if v_isSharedCheck_4952_ == 0 {
                    v___x_4940_ = v_head_4926_;
                    v_isShared_4941_ = v_isSharedCheck_4952_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_activeScopes_4937_);
                    lean_inc(v_state_4936_);
                    lean_dec(v_head_4926_);
                    v___x_4940_ = lean_box(0);
                    v_isShared_4941_ = v_isSharedCheck_4952_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4942_ = lean_apply_1(v_f_4923_, v_state_4936_);
                if v_isShared_4941_ == 0 {
                    lean_ctor_set(v___x_4940_, 0, v___x_4942_);
                    v___x_4944_ = v___x_4940_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4942_);
                    lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_activeScopes_4937_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4951_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_delimitsLocal_4938_,
                    );
                    v___x_4944_ = v_reuseFailAlloc_4951_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4935_ == 0 {
                    lean_ctor_set(v___x_4934_, 0, v___x_4944_);
                    v___x_4946_ = v___x_4934_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4944_);
                    lean_ctor_set(v_reuseFailAlloc_4950_, 1, v_tail_4932_);
                    v___x_4946_ = v_reuseFailAlloc_4950_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4931_ == 0 {
                    lean_ctor_set(v___x_4930_, 0, v___x_4946_);
                    v___x_4948_ = v___x_4930_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
                    lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_scopedEntries_4927_);
                    lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_newEntries_4928_);
                    v___x_4948_ = v_reuseFailAlloc_4949_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_modifyState___redArg(
    mut v_ext_4957_: *mut LeanObject,
    mut v_env_4958_: *mut LeanObject,
    mut v_f_4959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ext_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    v_ext_4960_ = lean_ctor_get(v_ext_4957_, 1);
    lean_inc_ref(v_ext_4960_);
    lean_dec_ref(v_ext_4957_);
    v_toEnvExtension_4961_ = lean_ctor_get(v_ext_4960_, 0);
    v_asyncMode_4962_ = lean_ctor_get(v_toEnvExtension_4961_, 2);
    lean_inc(v_asyncMode_4962_);
    v___f_4963_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_modifyState___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4963_, 0, v_f_4959_);
    v___x_4964_ = lean_box(0);
    v___x_4965_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
        v_ext_4960_,
        v_env_4958_,
        v___f_4963_,
        v_asyncMode_4962_,
        v___x_4964_,
    );
    lean_dec(v_asyncMode_4962_);
    return v___x_4965_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_modifyState(
    mut v_00_u03b1_4966_: *mut LeanObject,
    mut v_00_u03b2_4967_: *mut LeanObject,
    mut v_00_u03c3_4968_: *mut LeanObject,
    mut v_ext_4969_: *mut LeanObject,
    mut v_env_4970_: *mut LeanObject,
    mut v_f_4971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    v___x_4972_ =
        l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_4969_, v_env_4970_, v_f_4971_);
    return v___x_4972_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__0(
    mut v_toPure_4973_: *mut LeanObject,
    mut v_____s_4974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    v___x_4975_ = lean_box(0);
    v___x_4976_ = lean_apply_2(v_toPure_4973_, lean_box(0), v___x_4975_);
    return v___x_4976_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__1(
    mut v___x_4977_: *mut LeanObject,
    mut v_toPure_4978_: *mut LeanObject,
    mut v_r_4979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    v___x_4980_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4980_, 0, v___x_4977_);
    v___x_4981_ = lean_apply_2(v_toPure_4978_, lean_box(0), v___x_4980_);
    return v___x_4981_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__2(
    mut v_inst_4982_: *mut LeanObject,
    mut v_toBind_4983_: *mut LeanObject,
    mut v___f_4984_: *mut LeanObject,
    mut v_a_4985_: *mut LeanObject,
    mut v_x_4986_: *mut LeanObject,
    mut v___y_4987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_4988_ = lean_ctor_get(v_inst_4982_, 1);
    lean_inc(v_modifyEnv_4988_);
    lean_dec_ref(v_inst_4982_);
    v___x_4989_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_pushScope as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_4989_, 0, lean_box(0));
    lean_closure_set(v___x_4989_, 1, lean_box(0));
    lean_closure_set(v___x_4989_, 2, lean_box(0));
    lean_closure_set(v___x_4989_, 3, v_a_4985_);
    v___x_4990_ = lean_apply_1(v_modifyEnv_4988_, v___x_4989_);
    v___x_4991_ = lean_apply_4(
        v_toBind_4983_,
        lean_box(0),
        lean_box(0),
        v___x_4990_,
        v___f_4984_,
    );
    return v___x_4991_;
}
pub unsafe fn l_Lean_pushScope___redArg___lam__3(
    mut v_toPure_4992_: *mut LeanObject,
    mut v_inst_4993_: *mut LeanObject,
    mut v_toBind_4994_: *mut LeanObject,
    mut v_inst_4995_: *mut LeanObject,
    mut v___f_4996_: *mut LeanObject,
    mut v_____do__lift_4997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5001_: usize = 0;
    let mut v___x_5002_: usize = 0;
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    v___x_4998_ = lean_box(0);
    v___f_4999_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4999_, 0, v___x_4998_);
    lean_closure_set(v___f_4999_, 1, v_toPure_4992_);
    lean_inc(v_toBind_4994_);
    v___f_5000_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_5000_, 0, v_inst_4993_);
    lean_closure_set(v___f_5000_, 1, v_toBind_4994_);
    lean_closure_set(v___f_5000_, 2, v___f_4999_);
    v_sz_5001_ = lean_array_size(v_____do__lift_4997_);
    v___x_5002_ = 0usize;
    v___x_5003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_4995_,
        v_____do__lift_4997_,
        v___f_5000_,
        v_sz_5001_,
        v___x_5002_,
        v___x_4998_,
    );
    v___x_5004_ = lean_apply_4(
        v_toBind_4994_,
        lean_box(0),
        lean_box(0),
        v___x_5003_,
        v___f_4996_,
    );
    return v___x_5004_;
}
pub unsafe fn _init_l_Lean_pushScope___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    v___x_5005_ = l_Lean_scopedEnvExtensionsRef;
    v___x_5006_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_5006_, 0, lean_box(0));
    lean_closure_set(v___x_5006_, 1, lean_box(0));
    lean_closure_set(v___x_5006_, 2, v___x_5005_);
    return v___x_5006_;
}
pub unsafe fn l_Lean_pushScope___redArg(
    mut v_inst_5007_: *mut LeanObject,
    mut v_inst_5008_: *mut LeanObject,
    mut v_inst_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5010_ = lean_ctor_get(v_inst_5007_, 0);
    v_toBind_5011_ = lean_ctor_get(v_inst_5007_, 1);
    lean_inc_n(v_toBind_5011_, 2);
    v_toPure_5012_ = lean_ctor_get(v_toApplicative_5010_, 1);
    lean_inc_n(v_toPure_5012_, 2);
    v___x_5013_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5014_ = lean_apply_2(v_inst_5009_, lean_box(0), v___x_5013_);
    v___f_5015_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5015_, 0, v_toPure_5012_);
    v___f_5016_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_5016_, 0, v_toPure_5012_);
    lean_closure_set(v___f_5016_, 1, v_inst_5008_);
    lean_closure_set(v___f_5016_, 2, v_toBind_5011_);
    lean_closure_set(v___f_5016_, 3, v_inst_5007_);
    lean_closure_set(v___f_5016_, 4, v___f_5015_);
    v___x_5017_ = lean_apply_4(
        v_toBind_5011_,
        lean_box(0),
        lean_box(0),
        v___x_5014_,
        v___f_5016_,
    );
    return v___x_5017_;
}
pub unsafe fn l_Lean_pushScope(
    mut v_m_5018_: *mut LeanObject,
    mut v_inst_5019_: *mut LeanObject,
    mut v_inst_5020_: *mut LeanObject,
    mut v_inst_5021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    v___x_5022_ = l_Lean_pushScope___redArg(v_inst_5019_, v_inst_5020_, v_inst_5021_);
    return v___x_5022_;
}
pub unsafe fn l_Lean_popScope___redArg___lam__2(
    mut v_inst_5023_: *mut LeanObject,
    mut v_toBind_5024_: *mut LeanObject,
    mut v___f_5025_: *mut LeanObject,
    mut v_a_5026_: *mut LeanObject,
    mut v_x_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_5029_ = lean_ctor_get(v_inst_5023_, 1);
    lean_inc(v_modifyEnv_5029_);
    lean_dec_ref(v_inst_5023_);
    v___x_5030_ = lean_alloc_closure(
        l_Lean_ScopedEnvExtension_popScope as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_5030_, 0, lean_box(0));
    lean_closure_set(v___x_5030_, 1, lean_box(0));
    lean_closure_set(v___x_5030_, 2, lean_box(0));
    lean_closure_set(v___x_5030_, 3, v_a_5026_);
    v___x_5031_ = lean_apply_1(v_modifyEnv_5029_, v___x_5030_);
    v___x_5032_ = lean_apply_4(
        v_toBind_5024_,
        lean_box(0),
        lean_box(0),
        v___x_5031_,
        v___f_5025_,
    );
    return v___x_5032_;
}
pub unsafe fn l_Lean_popScope___redArg___lam__0(
    mut v_toPure_5033_: *mut LeanObject,
    mut v_inst_5034_: *mut LeanObject,
    mut v_toBind_5035_: *mut LeanObject,
    mut v_inst_5036_: *mut LeanObject,
    mut v___f_5037_: *mut LeanObject,
    mut v_____do__lift_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5042_: usize = 0;
    let mut v___x_5043_: usize = 0;
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    v___x_5039_ = lean_box(0);
    v___f_5040_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5040_, 0, v___x_5039_);
    lean_closure_set(v___f_5040_, 1, v_toPure_5033_);
    lean_inc(v_toBind_5035_);
    v___f_5041_ = lean_alloc_closure(
        l_Lean_popScope___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_5041_, 0, v_inst_5034_);
    lean_closure_set(v___f_5041_, 1, v_toBind_5035_);
    lean_closure_set(v___f_5041_, 2, v___f_5040_);
    v_sz_5042_ = lean_array_size(v_____do__lift_5038_);
    v___x_5043_ = 0usize;
    v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_5036_,
        v_____do__lift_5038_,
        v___f_5041_,
        v_sz_5042_,
        v___x_5043_,
        v___x_5039_,
    );
    v___x_5045_ = lean_apply_4(
        v_toBind_5035_,
        lean_box(0),
        lean_box(0),
        v___x_5044_,
        v___f_5037_,
    );
    return v___x_5045_;
}
pub unsafe fn l_Lean_popScope___redArg(
    mut v_inst_5046_: *mut LeanObject,
    mut v_inst_5047_: *mut LeanObject,
    mut v_inst_5048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5049_ = lean_ctor_get(v_inst_5046_, 0);
    v_toBind_5050_ = lean_ctor_get(v_inst_5046_, 1);
    lean_inc_n(v_toBind_5050_, 2);
    v_toPure_5051_ = lean_ctor_get(v_toApplicative_5049_, 1);
    lean_inc_n(v_toPure_5051_, 2);
    v___x_5052_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5053_ = lean_apply_2(v_inst_5048_, lean_box(0), v___x_5052_);
    v___f_5054_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5054_, 0, v_toPure_5051_);
    v___f_5055_ = lean_alloc_closure(
        l_Lean_popScope___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_5055_, 0, v_toPure_5051_);
    lean_closure_set(v___f_5055_, 1, v_inst_5047_);
    lean_closure_set(v___f_5055_, 2, v_toBind_5050_);
    lean_closure_set(v___f_5055_, 3, v_inst_5046_);
    lean_closure_set(v___f_5055_, 4, v___f_5054_);
    v___x_5056_ = lean_apply_4(
        v_toBind_5050_,
        lean_box(0),
        lean_box(0),
        v___x_5053_,
        v___f_5055_,
    );
    return v___x_5056_;
}
pub unsafe fn l_Lean_popScope(
    mut v_m_5057_: *mut LeanObject,
    mut v_inst_5058_: *mut LeanObject,
    mut v_inst_5059_: *mut LeanObject,
    mut v_inst_5060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    v___x_5061_ = l_Lean_popScope___redArg(v_inst_5058_, v_inst_5059_, v_inst_5060_);
    return v___x_5061_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg___lam__2(
    mut v_a_5062_: *mut LeanObject,
    mut v_depth_5063_: *mut LeanObject,
    mut v_x_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v___x_5065_ =
        l_Lean_ScopedEnvExtension_setDelimitsLocal___redArg(v_a_5062_, v_x_5064_, v_depth_5063_);
    return v___x_5065_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg___lam__0(
    mut v_inst_5066_: *mut LeanObject,
    mut v_depth_5067_: *mut LeanObject,
    mut v_toBind_5068_: *mut LeanObject,
    mut v___f_5069_: *mut LeanObject,
    mut v_a_5070_: *mut LeanObject,
    mut v_x_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_5073_ = lean_ctor_get(v_inst_5066_, 1);
    lean_inc(v_modifyEnv_5073_);
    lean_dec_ref(v_inst_5066_);
    v___f_5074_ = lean_alloc_closure(
        l_Lean_setDelimitsLocal___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5074_, 0, v_a_5070_);
    lean_closure_set(v___f_5074_, 1, v_depth_5067_);
    v___x_5075_ = lean_apply_1(v_modifyEnv_5073_, v___f_5074_);
    v___x_5076_ = lean_apply_4(
        v_toBind_5068_,
        lean_box(0),
        lean_box(0),
        v___x_5075_,
        v___f_5069_,
    );
    return v___x_5076_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg___lam__1(
    mut v_toPure_5077_: *mut LeanObject,
    mut v_inst_5078_: *mut LeanObject,
    mut v_depth_5079_: *mut LeanObject,
    mut v_toBind_5080_: *mut LeanObject,
    mut v_inst_5081_: *mut LeanObject,
    mut v___f_5082_: *mut LeanObject,
    mut v_____do__lift_5083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5087_: usize = 0;
    let mut v___x_5088_: usize = 0;
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    v___x_5084_ = lean_box(0);
    v___f_5085_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5085_, 0, v___x_5084_);
    lean_closure_set(v___f_5085_, 1, v_toPure_5077_);
    lean_inc(v_toBind_5080_);
    v___f_5086_ = lean_alloc_closure(
        l_Lean_setDelimitsLocal___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_5086_, 0, v_inst_5078_);
    lean_closure_set(v___f_5086_, 1, v_depth_5079_);
    lean_closure_set(v___f_5086_, 2, v_toBind_5080_);
    lean_closure_set(v___f_5086_, 3, v___f_5085_);
    v_sz_5087_ = lean_array_size(v_____do__lift_5083_);
    v___x_5088_ = 0usize;
    v___x_5089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_5081_,
        v_____do__lift_5083_,
        v___f_5086_,
        v_sz_5087_,
        v___x_5088_,
        v___x_5084_,
    );
    v___x_5090_ = lean_apply_4(
        v_toBind_5080_,
        lean_box(0),
        lean_box(0),
        v___x_5089_,
        v___f_5082_,
    );
    return v___x_5090_;
}
pub unsafe fn l_Lean_setDelimitsLocal___redArg(
    mut v_inst_5091_: *mut LeanObject,
    mut v_inst_5092_: *mut LeanObject,
    mut v_inst_5093_: *mut LeanObject,
    mut v_depth_5094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5095_ = lean_ctor_get(v_inst_5091_, 0);
    v_toBind_5096_ = lean_ctor_get(v_inst_5091_, 1);
    lean_inc_n(v_toBind_5096_, 2);
    v_toPure_5097_ = lean_ctor_get(v_toApplicative_5095_, 1);
    lean_inc_n(v_toPure_5097_, 2);
    v___x_5098_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5099_ = lean_apply_2(v_inst_5093_, lean_box(0), v___x_5098_);
    v___f_5100_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5100_, 0, v_toPure_5097_);
    v___f_5101_ = lean_alloc_closure(
        l_Lean_setDelimitsLocal___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_5101_, 0, v_toPure_5097_);
    lean_closure_set(v___f_5101_, 1, v_inst_5092_);
    lean_closure_set(v___f_5101_, 2, v_depth_5094_);
    lean_closure_set(v___f_5101_, 3, v_toBind_5096_);
    lean_closure_set(v___f_5101_, 4, v_inst_5091_);
    lean_closure_set(v___f_5101_, 5, v___f_5100_);
    v___x_5102_ = lean_apply_4(
        v_toBind_5096_,
        lean_box(0),
        lean_box(0),
        v___x_5099_,
        v___f_5101_,
    );
    return v___x_5102_;
}
pub unsafe fn l_Lean_setDelimitsLocal(
    mut v_m_5103_: *mut LeanObject,
    mut v_inst_5104_: *mut LeanObject,
    mut v_inst_5105_: *mut LeanObject,
    mut v_inst_5106_: *mut LeanObject,
    mut v_depth_5107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    v___x_5108_ =
        l_Lean_setDelimitsLocal___redArg(v_inst_5104_, v_inst_5105_, v_inst_5106_, v_depth_5107_);
    return v___x_5108_;
}
pub unsafe fn l_Lean_activateScoped___redArg___lam__2(
    mut v_a_5109_: *mut LeanObject,
    mut v_namespaceName_5110_: *mut LeanObject,
    mut v_x_5111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    v___x_5112_ = l_Lean_ScopedEnvExtension_activateScoped___redArg(
        v_a_5109_,
        v_x_5111_,
        v_namespaceName_5110_,
    );
    return v___x_5112_;
}
pub unsafe fn l_Lean_activateScoped___redArg___lam__0(
    mut v_inst_5113_: *mut LeanObject,
    mut v_namespaceName_5114_: *mut LeanObject,
    mut v_toBind_5115_: *mut LeanObject,
    mut v___f_5116_: *mut LeanObject,
    mut v_a_5117_: *mut LeanObject,
    mut v_x_5118_: *mut LeanObject,
    mut v___y_5119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyEnv_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_5120_ = lean_ctor_get(v_inst_5113_, 1);
    lean_inc(v_modifyEnv_5120_);
    lean_dec_ref(v_inst_5113_);
    v___f_5121_ = lean_alloc_closure(
        l_Lean_activateScoped___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5121_, 0, v_a_5117_);
    lean_closure_set(v___f_5121_, 1, v_namespaceName_5114_);
    v___x_5122_ = lean_apply_1(v_modifyEnv_5120_, v___f_5121_);
    v___x_5123_ = lean_apply_4(
        v_toBind_5115_,
        lean_box(0),
        lean_box(0),
        v___x_5122_,
        v___f_5116_,
    );
    return v___x_5123_;
}
pub unsafe fn l_Lean_activateScoped___redArg___lam__1(
    mut v_toPure_5124_: *mut LeanObject,
    mut v_inst_5125_: *mut LeanObject,
    mut v_namespaceName_5126_: *mut LeanObject,
    mut v_toBind_5127_: *mut LeanObject,
    mut v_inst_5128_: *mut LeanObject,
    mut v___f_5129_: *mut LeanObject,
    mut v_____do__lift_5130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5134_: usize = 0;
    let mut v___x_5135_: usize = 0;
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    v___x_5131_ = lean_box(0);
    v___f_5132_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5132_, 0, v___x_5131_);
    lean_closure_set(v___f_5132_, 1, v_toPure_5124_);
    lean_inc(v_toBind_5127_);
    v___f_5133_ = lean_alloc_closure(
        l_Lean_activateScoped___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_5133_, 0, v_inst_5125_);
    lean_closure_set(v___f_5133_, 1, v_namespaceName_5126_);
    lean_closure_set(v___f_5133_, 2, v_toBind_5127_);
    lean_closure_set(v___f_5133_, 3, v___f_5132_);
    v_sz_5134_ = lean_array_size(v_____do__lift_5130_);
    v___x_5135_ = 0usize;
    v___x_5136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_5128_,
        v_____do__lift_5130_,
        v___f_5133_,
        v_sz_5134_,
        v___x_5135_,
        v___x_5131_,
    );
    v___x_5137_ = lean_apply_4(
        v_toBind_5127_,
        lean_box(0),
        lean_box(0),
        v___x_5136_,
        v___f_5129_,
    );
    return v___x_5137_;
}
pub unsafe fn l_Lean_activateScoped___redArg(
    mut v_inst_5138_: *mut LeanObject,
    mut v_inst_5139_: *mut LeanObject,
    mut v_inst_5140_: *mut LeanObject,
    mut v_namespaceName_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5142_ = lean_ctor_get(v_inst_5138_, 0);
    v_toBind_5143_ = lean_ctor_get(v_inst_5138_, 1);
    lean_inc_n(v_toBind_5143_, 2);
    v_toPure_5144_ = lean_ctor_get(v_toApplicative_5142_, 1);
    lean_inc_n(v_toPure_5144_, 2);
    v___x_5145_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_pushScope___redArg___closed__0_once),
        _init_l_Lean_pushScope___redArg___closed__0,
    );
    v___x_5146_ = lean_apply_2(v_inst_5140_, lean_box(0), v___x_5145_);
    v___f_5147_ = lean_alloc_closure(
        l_Lean_pushScope___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5147_, 0, v_toPure_5144_);
    v___f_5148_ = lean_alloc_closure(
        l_Lean_activateScoped___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_5148_, 0, v_toPure_5144_);
    lean_closure_set(v___f_5148_, 1, v_inst_5139_);
    lean_closure_set(v___f_5148_, 2, v_namespaceName_5141_);
    lean_closure_set(v___f_5148_, 3, v_toBind_5143_);
    lean_closure_set(v___f_5148_, 4, v_inst_5138_);
    lean_closure_set(v___f_5148_, 5, v___f_5147_);
    v___x_5149_ = lean_apply_4(
        v_toBind_5143_,
        lean_box(0),
        lean_box(0),
        v___x_5146_,
        v___f_5148_,
    );
    return v___x_5149_;
}
pub unsafe fn l_Lean_activateScoped(
    mut v_m_5150_: *mut LeanObject,
    mut v_inst_5151_: *mut LeanObject,
    mut v_inst_5152_: *mut LeanObject,
    mut v_inst_5153_: *mut LeanObject,
    mut v_namespaceName_5154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    v___x_5155_ = l_Lean_activateScoped___redArg(
        v_inst_5151_,
        v_inst_5152_,
        v_inst_5153_,
        v_namespaceName_5154_,
    );
    return v___x_5155_;
}
pub unsafe fn _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam() -> *mut LeanObject {
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    v___x_5156_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28),
        core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28_once),
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam___closed__28,
    );
    return v___x_5156_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(
    mut v___y_5157_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___y_5157_);
    return v___y_5157_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0___boxed(
    mut v___y_5158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5159_: *mut LeanObject = core::ptr::null_mut();
    v_res_5159_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__0(v___y_5158_);
    lean_dec(v___y_5158_);
    return v_res_5159_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(
    mut v_x_5160_: *mut LeanObject,
    mut v_a_5161_: *mut LeanObject,
    mut v___y_5162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    v___x_5164_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5164_, 0, v_a_5161_);
    return v___x_5164_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1___boxed(
    mut v_x_5165_: *mut LeanObject,
    mut v_a_5166_: *mut LeanObject,
    mut v___y_5167_: *mut LeanObject,
    mut v___y_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5169_: *mut LeanObject = core::ptr::null_mut();
    v_res_5169_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__1(
        v_x_5165_,
        v_a_5166_,
        v___y_5167_,
    );
    lean_dec_ref(v___y_5167_);
    lean_dec(v_x_5165_);
    return v_res_5169_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(
    mut v_initial_5170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    v___x_5172_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5172_, 0, v_initial_5170_);
    return v___x_5172_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed(
    mut v_initial_5173_: *mut LeanObject,
    mut v___y_5174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5175_: *mut LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2(v_initial_5173_);
    return v_res_5175_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg(
    mut v_descr_5178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addEntry_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initial_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finalizeImport_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exportEntry_x3f_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    v_name_5180_ = lean_ctor_get(v_descr_5178_, 0);
    lean_inc(v_name_5180_);
    v_addEntry_5181_ = lean_ctor_get(v_descr_5178_, 1);
    lean_inc(v_addEntry_5181_);
    v_initial_5182_ = lean_ctor_get(v_descr_5178_, 2);
    lean_inc(v_initial_5182_);
    v_finalizeImport_5183_ = lean_ctor_get(v_descr_5178_, 3);
    lean_inc(v_finalizeImport_5183_);
    v_exportEntry_x3f_5184_ = lean_ctor_get(v_descr_5178_, 4);
    lean_inc_ref(v_exportEntry_x3f_5184_);
    lean_dec_ref(v_descr_5178_);
    v___f_5185_ = l_Lean_registerSimpleScopedEnvExtension___redArg___closed__0;
    v___f_5186_ = l_Lean_registerSimpleScopedEnvExtension___redArg___closed__1;
    v___f_5187_ = lean_alloc_closure(
        l_Lean_registerSimpleScopedEnvExtension___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5187_, 0, v_initial_5182_);
    v___x_5188_ = lean_alloc_ctor(0, 7, (0) as u32);
    lean_ctor_set(v___x_5188_, 0, v_name_5180_);
    lean_ctor_set(v___x_5188_, 1, v___f_5187_);
    lean_ctor_set(v___x_5188_, 2, v___f_5186_);
    lean_ctor_set(v___x_5188_, 3, v___f_5185_);
    lean_ctor_set(v___x_5188_, 4, v_addEntry_5181_);
    lean_ctor_set(v___x_5188_, 5, v_finalizeImport_5183_);
    lean_ctor_set(v___x_5188_, 6, v_exportEntry_x3f_5184_);
    v___x_5189_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_5188_);
    return v___x_5189_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___redArg___boxed(
    mut v_descr_5190_: *mut LeanObject,
    mut v_a_5191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5192_: *mut LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_5190_);
    return v_res_5192_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension(
    mut v_00_u03b1_5193_: *mut LeanObject,
    mut v_00_u03c3_5194_: *mut LeanObject,
    mut v_descr_5195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    v___x_5197_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v_descr_5195_);
    return v___x_5197_;
}
pub unsafe fn l_Lean_registerSimpleScopedEnvExtension___boxed(
    mut v_00_u03b1_5198_: *mut LeanObject,
    mut v_00_u03c3_5199_: *mut LeanObject,
    mut v_descr_5200_: *mut LeanObject,
    mut v_a_5201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5202_: *mut LeanObject = core::ptr::null_mut();
    v_res_5202_ =
        l_Lean_registerSimpleScopedEnvExtension(v_00_u03b1_5198_, v_00_u03c3_5199_, v_descr_5200_);
    return v_res_5202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ScopedEnvExtension(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_ScopedEnvExtension_0__Lean_initFn_00___x40_Lean_ScopedEnvExtension_3284267871____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_scopedEnvExtensionsRef = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_scopedEnvExtensionsRef);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ScopedEnvExtension(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_ScopedEnvExtension_Descr_name___autoParam =
        _init_l_Lean_ScopedEnvExtension_Descr_name___autoParam();
    lean_mark_persistent(l_Lean_ScopedEnvExtension_Descr_name___autoParam);
    l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam =
        _init_l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam();
    lean_mark_persistent(l_Lean_SimpleScopedEnvExtension_Descr_name___autoParam);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ScopedEnvExtension(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_ScopedEnvExtension(builtin);
}
