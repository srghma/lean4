// Lean compiler output
// Module: Lean.Compiler.ModPkgExt
// Imports: Lean.Environment Lean.Compiler.NameMangling
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_mkAtom,
};
use crate::r#gen::Lean::Compiler::NameMangling::{
    initialize_Lean_Compiler_NameMangling, l_Lean_Name_mangle, l_Lean_mkPackageSymbolPrefix,
    runtime_initialize_Lean_Compiler_NameMangling,
};
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_PersistentEnvExtension_setState___redArg, l_Lean_instInhabitedEnvExtension_default,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg, runtime_initialize_Lean_Environment,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__10_value: LeanStringObject<6> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__11_value: LeanCtorObject<3> =
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
                l_Lean_registerModuleEnvExtension___auto__1___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__14_value: LeanStringObject<5> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__15_value: LeanStringObject<9> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__15_value)
        as *mut LeanObject;
static l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__16_value: LeanCtorObject<3> =
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
                l_Lean_registerModuleEnvExtension___auto__1___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__15_value)
                as *mut LeanObject,
            7677164612348466033 as *mut LeanObject,
        ],
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___auto__1___closed__17_value: LeanStringObject<11> =
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
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__17_value)
        as *mut LeanObject;
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_registerModuleEnvExtension___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_registerModuleEnvExtension___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_registerModuleEnvExtension___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerModuleEnvExtension___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerModuleEnvExtension___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerModuleEnvExtension___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_registerModuleEnvExtension___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_registerModuleEnvExtension___redArg___lam__4 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_registerModuleEnvExtension___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0_value:
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
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1_value:
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
        l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0_value:
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
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__1_value:
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
            l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1_value: LeanClosureObject<
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
    m_fun: l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [77, 111, 100, 80, 107, 103, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__6_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,16617064250654575691 as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__7_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,5073107430785488950 as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__8_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_registerModuleEnvExtension___auto__1___closed__0_value) as *mut LeanObject,7932200623308891999 as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 111, 100, 80, 107, 103, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__9_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__10_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject,6050880569427789747 as *mut LeanObject] };
static mut l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Lean_registerModuleEnvExtension___auto__1___closed__10;
    v___x_313_ = l_Lean_mkAtom(v___x_312_);
    return v___x_313_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    v___x_314_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__12_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__12,
    );
    v___x_315_ = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
    v___x_316_ = lean_array_push(v___x_315_, v___x_314_);
    return v___x_316_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    v___x_325_ = l_Lean_registerModuleEnvExtension___auto__1___closed__17;
    v___x_326_ = l_Lean_mkAtom(v___x_325_);
    return v___x_326_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    v___x_327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__18_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__18,
    );
    v___x_328_ = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
    v___x_329_ = lean_array_push(v___x_328_, v___x_327_);
    return v___x_329_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    v___x_330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__19_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__19,
    );
    v___x_331_ = l_Lean_registerModuleEnvExtension___auto__1___closed__16;
    v___x_332_ = lean_box(2);
    v___x_333_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_333_, 0, v___x_332_);
    lean_ctor_set(v___x_333_, 1, v___x_331_);
    lean_ctor_set(v___x_333_, 2, v___x_330_);
    return v___x_333_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___x_334_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__20_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__20,
    );
    v___x_335_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__13_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__13,
    );
    v___x_336_ = lean_array_push(v___x_335_, v___x_334_);
    return v___x_336_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__21_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__21,
    );
    v___x_338_ = l_Lean_registerModuleEnvExtension___auto__1___closed__11;
    v___x_339_ = lean_box(2);
    v___x_340_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_340_, 0, v___x_339_);
    lean_ctor_set(v___x_340_, 1, v___x_338_);
    lean_ctor_set(v___x_340_, 2, v___x_337_);
    return v___x_340_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    v___x_341_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__22_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__22,
    );
    v___x_342_ = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
    v___x_343_ = lean_array_push(v___x_342_, v___x_341_);
    return v___x_343_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    v___x_344_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__23_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__23,
    );
    v___x_345_ = l_Lean_registerModuleEnvExtension___auto__1___closed__9;
    v___x_346_ = lean_box(2);
    v___x_347_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_347_, 0, v___x_346_);
    lean_ctor_set(v___x_347_, 1, v___x_345_);
    lean_ctor_set(v___x_347_, 2, v___x_344_);
    return v___x_347_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__24_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__24,
    );
    v___x_349_ = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
    v___x_350_ = lean_array_push(v___x_349_, v___x_348_);
    return v___x_350_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__25_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__25,
    );
    v___x_352_ = l_Lean_registerModuleEnvExtension___auto__1___closed__7;
    v___x_353_ = lean_box(2);
    v___x_354_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_354_, 0, v___x_353_);
    lean_ctor_set(v___x_354_, 1, v___x_352_);
    lean_ctor_set(v___x_354_, 2, v___x_351_);
    return v___x_354_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__26_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__26,
    );
    v___x_356_ = l_Lean_registerModuleEnvExtension___auto__1___closed__5;
    v___x_357_ = lean_array_push(v___x_356_, v___x_355_);
    return v___x_357_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__27_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__27,
    );
    v___x_359_ = l_Lean_registerModuleEnvExtension___auto__1___closed__4;
    v___x_360_ = lean_box(2);
    v___x_361_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_361_, 0, v___x_360_);
    lean_ctor_set(v___x_361_, 1, v___x_359_);
    lean_ctor_set(v___x_361_, 2, v___x_358_);
    return v___x_361_;
}
pub unsafe fn _init_l_Lean_registerModuleEnvExtension___auto__1() -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_registerModuleEnvExtension___auto__1___closed__28_once),
        _init_l_Lean_registerModuleEnvExtension___auto__1___closed__28,
    );
    return v___x_362_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__0(
    mut v_mkInitial_363_: *mut LeanObject,
    mut v_x_364_: *mut LeanObject,
    mut v_x_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    v___x_367_ = lean_apply_1(v_mkInitial_363_, lean_box(0));
    return v___x_367_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed(
    mut v_mkInitial_368_: *mut LeanObject,
    mut v_x_369_: *mut LeanObject,
    mut v_x_370_: *mut LeanObject,
    mut v___y_371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_372_: *mut LeanObject = core::ptr::null_mut();
    v_res_372_ =
        l_Lean_registerModuleEnvExtension___redArg___lam__0(v_mkInitial_368_, v_x_369_, v_x_370_);
    lean_dec_ref(v_x_370_);
    lean_dec_ref(v_x_369_);
    return v_res_372_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__1(
    mut v_s_373_: *mut LeanObject,
    mut v_x_374_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_s_373_);
    return v_s_373_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__1___boxed(
    mut v_s_375_: *mut LeanObject,
    mut v_x_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_377_: *mut LeanObject = core::ptr::null_mut();
    v_res_377_ = l_Lean_registerModuleEnvExtension___redArg___lam__1(v_s_375_, v_x_376_);
    lean_dec(v_x_376_);
    lean_dec(v_s_375_);
    return v_res_377_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__2(
    mut v_x_378_: *mut LeanObject,
    mut v_s_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = lean_unsigned_to_nat(1);
    v___x_381_ = lean_mk_empty_array_with_capacity(v___x_380_);
    v___x_382_ = lean_array_push(v___x_381_, v_s_379_);
    lean_inc_ref_n(v___x_382_, 2);
    v___x_383_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_383_, 0, v___x_382_);
    lean_ctor_set(v___x_383_, 1, v___x_382_);
    lean_ctor_set(v___x_383_, 2, v___x_382_);
    return v___x_383_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__2___boxed(
    mut v_x_384_: *mut LeanObject,
    mut v_s_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_386_: *mut LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Lean_registerModuleEnvExtension___redArg___lam__2(v_x_384_, v_s_385_);
    lean_dec_ref(v_x_384_);
    return v_res_386_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__3(
    mut v_x_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    v___x_388_ = lean_box(0);
    return v___x_388_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__3___boxed(
    mut v_x_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_390_: *mut LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Lean_registerModuleEnvExtension___redArg___lam__3(v_x_389_);
    lean_dec(v_x_389_);
    return v_res_390_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___lam__4(
    mut v_s_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = lean_unsigned_to_nat(1);
    v___x_393_ = lean_mk_empty_array_with_capacity(v___x_392_);
    v___x_394_ = lean_array_push(v___x_393_, v_s_391_);
    return v___x_394_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg(
    mut v_mkInitial_399_: *mut LeanObject,
    mut v_name_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_mkInitial_399_);
    v___f_402_ = lean_alloc_closure(
        l_Lean_registerModuleEnvExtension___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_402_, 0, v_mkInitial_399_);
    v___f_403_ = l_Lean_registerModuleEnvExtension___redArg___closed__0;
    v___f_404_ = l_Lean_registerModuleEnvExtension___redArg___closed__1;
    v___f_405_ = l_Lean_registerModuleEnvExtension___redArg___closed__2;
    v___f_406_ = l_Lean_registerModuleEnvExtension___redArg___closed__3;
    v___x_407_ = lean_box(2);
    v___x_408_ = lean_box(0);
    v___x_409_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_409_, 0, v_name_400_);
    lean_ctor_set(v___x_409_, 1, v_mkInitial_399_);
    lean_ctor_set(v___x_409_, 2, v___f_402_);
    lean_ctor_set(v___x_409_, 3, v___f_403_);
    lean_ctor_set(v___x_409_, 4, v___f_404_);
    lean_ctor_set(v___x_409_, 5, v___f_405_);
    lean_ctor_set(v___x_409_, 6, v___x_407_);
    lean_ctor_set(v___x_409_, 7, v___x_408_);
    v___x_410_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_410_, 0, v___x_409_);
    lean_ctor_set(v___x_410_, 1, v___f_406_);
    v___x_411_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_410_);
    return v___x_411_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___redArg___boxed(
    mut v_mkInitial_412_: *mut LeanObject,
    mut v_name_413_: *mut LeanObject,
    mut v_a_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_415_: *mut LeanObject = core::ptr::null_mut();
    v_res_415_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_412_, v_name_413_);
    return v_res_415_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension(
    mut v_00_u03c3_416_: *mut LeanObject,
    mut v_inst_417_: *mut LeanObject,
    mut v_mkInitial_418_: *mut LeanObject,
    mut v_name_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    v___x_421_ = l_Lean_registerModuleEnvExtension___redArg(v_mkInitial_418_, v_name_419_);
    return v___x_421_;
}
pub unsafe fn l_Lean_registerModuleEnvExtension___boxed(
    mut v_00_u03c3_422_: *mut LeanObject,
    mut v_inst_423_: *mut LeanObject,
    mut v_mkInitial_424_: *mut LeanObject,
    mut v_name_425_: *mut LeanObject,
    mut v_a_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_427_: *mut LeanObject = core::ptr::null_mut();
    v_res_427_ = l_Lean_registerModuleEnvExtension(
        v_00_u03c3_422_,
        v_inst_423_,
        v_mkInitial_424_,
        v_name_425_,
    );
    lean_dec(v_inst_423_);
    return v_res_427_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0(
    mut v_x_431_: *mut LeanObject,
    mut v___y_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    v___x_434_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___closed__1;
    v___x_435_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_435_, 0, v___x_434_);
    return v___x_435_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0___boxed(
    mut v_x_436_: *mut LeanObject,
    mut v___y_437_: *mut LeanObject,
    mut v___y_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_439_: *mut LeanObject = core::ptr::null_mut();
    v_res_439_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__0(v_x_436_, v___y_437_);
    lean_dec_ref(v___y_437_);
    lean_dec_ref(v_x_436_);
    return v_res_439_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2(
    mut v_x_444_: *mut LeanObject,
    mut v_x_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___closed__1;
    return v___x_446_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2___boxed(
    mut v_x_447_: *mut LeanObject,
    mut v_x_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___lam__2(v_x_447_, v_x_448_);
    lean_dec(v_x_448_);
    lean_dec_ref(v_x_447_);
    return v_res_449_;
}
pub unsafe fn _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2() -> *mut LeanObject
{
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    v___x_452_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
    return v___x_452_;
}
pub unsafe fn _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3() -> *mut LeanObject
{
    let mut v___f_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    v___f_453_ = l_Lean_registerModuleEnvExtension___redArg___closed__2;
    v___f_454_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__1;
    v___f_455_ = l_Lean_registerModuleEnvExtension___redArg___closed__0;
    v___f_456_ = l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__0;
    v___x_457_ = lean_box(0);
    v___x_458_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2_once),
        _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__2,
    );
    v___x_459_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_459_, 0, v___x_458_);
    lean_ctor_set(v___x_459_, 1, v___x_457_);
    lean_ctor_set(v___x_459_, 2, v___f_456_);
    lean_ctor_set(v___x_459_, 3, v___f_455_);
    lean_ctor_set(v___x_459_, 4, v___f_454_);
    lean_ctor_set(v___x_459_, 5, v___f_453_);
    return v___x_459_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_instInhabited___aux__1(
    mut v_00_u03c3_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v___x_461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3_once),
        _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3,
    );
    return v___x_461_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_instInhabited(
    mut v_00_u03c3_462_: *mut LeanObject,
    mut v_inst_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    v___x_464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3),
        core::ptr::addr_of_mut!(l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3_once),
        _init_l_Lean_ModuleEnvExtension_instInhabited___aux__1___closed__3,
    );
    return v___x_464_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_instInhabited___boxed(
    mut v_00_u03c3_465_: *mut LeanObject,
    mut v_inst_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_467_: *mut LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Lean_ModuleEnvExtension_instInhabited(v_00_u03c3_465_, v_inst_466_);
    lean_dec(v_inst_466_);
    return v_res_467_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(
    mut v_inst_468_: *mut LeanObject,
    mut v_ext_469_: *mut LeanObject,
    mut v_env_470_: *mut LeanObject,
    mut v_idx_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: u8 = 0;
    v___x_472_ = 0;
    v___x_473_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
        v_inst_468_,
        v_ext_469_,
        v_env_470_,
        v_idx_471_,
        v___x_472_,
    );
    v___x_474_ = lean_unsigned_to_nat(0);
    v___x_475_ = lean_array_get_size(v___x_473_);
    v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
    if v___x_476_ == 0 {
        let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_473_);
        v___x_477_ = lean_box(0);
        return v___x_477_;
    } else {
        let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
        v___x_478_ = lean_array_fget(v___x_473_, v___x_474_);
        lean_dec_ref(v___x_473_);
        v___x_479_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_479_, 0, v___x_478_);
        return v___x_479_;
    }
}
pub unsafe fn l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg___boxed(
    mut v_inst_480_: *mut LeanObject,
    mut v_ext_481_: *mut LeanObject,
    mut v_env_482_: *mut LeanObject,
    mut v_idx_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_484_: *mut LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(
        v_inst_480_,
        v_ext_481_,
        v_env_482_,
        v_idx_483_,
    );
    lean_dec(v_idx_483_);
    lean_dec_ref(v_env_482_);
    lean_dec_ref(v_ext_481_);
    return v_res_484_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_getStateByIdx_x3f(
    mut v_00_u03c3_485_: *mut LeanObject,
    mut v_inst_486_: *mut LeanObject,
    mut v_ext_487_: *mut LeanObject,
    mut v_env_488_: *mut LeanObject,
    mut v_idx_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(
        v_inst_486_,
        v_ext_487_,
        v_env_488_,
        v_idx_489_,
    );
    return v___x_490_;
}
pub unsafe fn l_Lean_ModuleEnvExtension_getStateByIdx_x3f___boxed(
    mut v_00_u03c3_491_: *mut LeanObject,
    mut v_inst_492_: *mut LeanObject,
    mut v_ext_493_: *mut LeanObject,
    mut v_env_494_: *mut LeanObject,
    mut v_idx_495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_496_: *mut LeanObject = core::ptr::null_mut();
    v_res_496_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f(
        v_00_u03c3_491_,
        v_inst_492_,
        v_ext_493_,
        v_env_494_,
        v_idx_495_,
    );
    lean_dec(v_idx_495_);
    lean_dec_ref(v_env_494_);
    lean_dec_ref(v_ext_493_);
    return v_res_496_;
}
pub unsafe fn l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(
    mut v___x_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_499_, 0, v___x_497_);
    return v___x_499_;
}
pub unsafe fn l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(
    mut v___x_500_: *mut LeanObject,
    mut v___y_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_res_502_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_(v___x_500_);
    return v_res_502_;
}
pub unsafe fn l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v___f_531_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_;
    v___x_532_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn___closed__11_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_;
    v___x_533_ = l_Lean_registerModuleEnvExtension___redArg(v___f_531_, v___x_532_);
    return v___x_533_;
}
pub unsafe fn l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2____boxed(
    mut v_a_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_535_: *mut LeanObject = core::ptr::null_mut();
    v_res_535_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_();
    return v_res_535_;
}
pub unsafe fn l_Lean_Environment_getModulePackageByIdx_x3f(
    mut v_env_536_: *mut LeanObject,
    mut v_idx_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    v___x_538_ = lean_box(0);
    v___x_539_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
    v___x_540_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(
        v___x_538_, v___x_539_, v_env_536_, v_idx_537_,
    );
    if lean_obj_tag(v___x_540_) == 0 {
        return v___x_538_;
    } else {
        let mut v_val_541_: *mut LeanObject = core::ptr::null_mut();
        v_val_541_ = lean_ctor_get(v___x_540_, 0);
        lean_inc(v_val_541_);
        lean_dec_ref_known(v___x_540_, 1);
        return v_val_541_;
    }
}
pub unsafe fn l_Lean_Environment_getModulePackageByIdx_x3f___boxed(
    mut v_env_542_: *mut LeanObject,
    mut v_idx_543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_544_: *mut LeanObject = core::ptr::null_mut();
    v_res_544_ = l_Lean_Environment_getModulePackageByIdx_x3f(v_env_542_, v_idx_543_);
    lean_dec(v_idx_543_);
    lean_dec_ref(v_env_542_);
    return v_res_544_;
}
pub unsafe fn l_Lean_Environment_getModulePackage_x3f(
    mut v_env_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    v___x_546_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
    v_toEnvExtension_547_ = lean_ctor_get(v___x_546_, 0);
    v_asyncMode_548_ = lean_ctor_get(v_toEnvExtension_547_, 2);
    v___x_549_ = lean_box(0);
    v___x_550_ = lean_box(0);
    v___x_551_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_549_,
        v___x_546_,
        v_env_545_,
        v_asyncMode_548_,
        v___x_550_,
    );
    return v___x_551_;
}
pub unsafe fn l_Lean_Environment_setModulePackage(
    mut v_pkg_x3f_552_: *mut LeanObject,
    mut v_env_553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    v___x_554_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
    v___x_555_ =
        l_Lean_PersistentEnvExtension_setState___redArg(v___x_554_, v_env_553_, v_pkg_x3f_552_);
    return v___x_555_;
}
pub unsafe fn lean_get_symbol_stem(
    mut v_env_556_: *mut LeanObject,
    mut v_declName_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_562_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_556_, v_declName_557_);
                if lean_obj_tag(v___x_562_) == 0 {
                    v___x_563_ = l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt;
                    v_toEnvExtension_564_ = lean_ctor_get(v___x_563_, 0);
                    v_asyncMode_565_ = lean_ctor_get(v_toEnvExtension_564_, 2);
                    v___x_566_ = lean_box(0);
                    v___x_567_ = lean_box(0);
                    v___x_568_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_566_,
                        v___x_563_,
                        v_env_556_,
                        v_asyncMode_565_,
                        v___x_567_,
                    );
                    v___y_559_ = v___x_568_;
                    state = 1;
                    continue;
                } else {
                    v_val_569_ = lean_ctor_get(v___x_562_, 0);
                    lean_inc(v_val_569_);
                    lean_dec_ref_known(v___x_562_, 1);
                    v___x_570_ =
                        l_Lean_Environment_getModulePackageByIdx_x3f(v_env_556_, v_val_569_);
                    lean_dec(v_val_569_);
                    lean_dec_ref(v_env_556_);
                    v___y_559_ = v___x_570_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_560_ = l_Lean_mkPackageSymbolPrefix(v___y_559_);
                lean_dec(v___y_559_);
                v___x_561_ = l_Lean_Name_mangle(v_declName_557_, v___x_560_);
                return v___x_561_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_ModPkgExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_ModPkgExt_0__Lean_initFn_00___x40_Lean_Compiler_ModPkgExt_2096304058____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt = lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_Compiler_ModPkgExt_0__Lean_modPkgExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_ModPkgExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_registerModuleEnvExtension___auto__1 =
        _init_l_Lean_registerModuleEnvExtension___auto__1();
    lean_mark_persistent(l_Lean_registerModuleEnvExtension___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_ModPkgExt(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Environment(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_NameMangling(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_ModPkgExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_ModPkgExt(builtin);
}
