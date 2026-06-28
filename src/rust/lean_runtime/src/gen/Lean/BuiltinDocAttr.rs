// Lean compiler output
// Module: Lean.BuiltinDocAttr
// Imports: Lean.Compiler.InitAttr
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::AuxRecursor::{l_Lean_isAuxRecursor, l_Lean_isNoConfusion};
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, l_Lean_declareBuiltin,
    runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Data::DeclarationRange::l_Lean_instInhabitedDeclarationRanges_default;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_getPrefix;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::{l_Lean_builtinDeclRanges, l_Lean_declRangeExt};
use crate::r#gen::Lean::DocString::Extension::{
    l_Lean_addBuiltinDocString, l_Lean_findSimpleDocString_x3f,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_MapDeclarationExtension_find_x3f___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkStrLit};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isRecCore;
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__1_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            97, 100, 100, 66, 117, 105, 108, 116, 105, 110, 68, 101, 99, 108, 97, 114, 97, 116,
            105, 111, 110, 82, 97, 110, 103, 101, 115, 0,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__1_value)
        as *mut LeanObject;
static l_Lean_declareBuiltinDocStringAndRanges___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__1_value)
                as *mut LeanObject,
            3642648952962374387 as *mut LeanObject,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__4_value: LeanStringObject<18> =
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
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__5_value: LeanStringObject<3> =
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
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__5_value)
        as *mut LeanObject;
static l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__4_value)
                as *mut LeanObject,
            4956747414454776495 as *mut LeanObject,
        ],
    };
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__5_value)
                as *mut LeanObject,
            15960823074304203395 as *mut LeanObject,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__8_value: LeanStringObject<17> =
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
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__8_value)
        as *mut LeanObject;
static l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__8_value)
                as *mut LeanObject,
            9209224823825377344 as *mut LeanObject,
        ],
    };
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__9_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__5_value)
                as *mut LeanObject,
            3831656119348534840 as *mut LeanObject,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__11_value: LeanStringObject<9> =
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
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__11_value)
        as *mut LeanObject;
static l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__11_value)
                as *mut LeanObject,
            7283224396379583297 as *mut LeanObject,
        ],
    };
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__12_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__5_value)
                as *mut LeanObject,
            11125062533858197709 as *mut LeanObject,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__14_value: LeanStringObject<10> =
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
        m_data: [100, 101, 99, 108, 82, 97, 110, 103, 101, 0],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__14_value)
                as *mut LeanObject,
            3368703879269978082 as *mut LeanObject,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__16_value: LeanStringObject<10> =
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
        m_data: [100, 111, 99, 83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__16_value)
                as *mut LeanObject,
            9257498773915394556 as *mut LeanObject,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__18_value: LeanStringObject<20> =
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
            97, 100, 100, 66, 117, 105, 108, 116, 105, 110, 68, 111, 99, 83, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__18_value)
        as *mut LeanObject;
static l_Lean_declareBuiltinDocStringAndRanges___closed__19_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_declareBuiltinDocStringAndRanges___closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__19_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__18_value)
                as *mut LeanObject,
            861836487704027913 as *mut LeanObject,
        ],
    };
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_declareBuiltinDocStringAndRanges___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [66, 117, 105, 108, 116, 105, 110, 68, 111, 99, 65, 116, 116, 114, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,6808791154970104923 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__5_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,7914483854525380326 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__6_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value) as *mut LeanObject,14056780180639000175 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__7_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__8_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,7903102204134431086 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__9_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__10_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,16493643965182017007 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__11_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_declareBuiltinDocStringAndRanges___closed__0_value) as *mut LeanObject,16632509256797084802 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__12_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__4_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,5690729320013976259 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__13_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,((( 939411776 as usize) << 1) | 1) as *mut LeanObject,5333431167162822202 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__14_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__15_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,3224612595156022293 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__16_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__17_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,12701672682430326741 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__18_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,7296328223709338456 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 100, 111, 99, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__20_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,4497599896277257119 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<70> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 70, m_capacity: 70, m_length: 69, m_data: [109, 97, 107, 101, 32, 116, 104, 101, 32, 100, 111, 99, 115, 32, 97, 110, 100, 32, 108, 111, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 105, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 97, 115, 32, 97, 32, 98, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__21_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__23_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__24_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__22_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value: LeanStringObject<291> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 291, m_capacity: 291, m_length: 290, m_data: [77, 97, 107, 101, 115, 32, 116, 104, 101, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 97, 110, 100, 32, 108, 111, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 97, 115, 32, 97, 32, 98, 117, 105, 108, 116, 105, 110, 46, 10, 10, 84, 104, 105, 115, 32, 97, 108, 108, 111, 119, 115, 32, 116, 104, 101, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 111, 102, 32, 99, 111, 114, 101, 32, 76, 101, 97, 110, 32, 102, 101, 97, 116, 117, 114, 101, 115, 32, 116, 111, 32, 98, 101, 32, 118, 105, 115, 105, 98, 108, 101, 32, 119, 105, 116, 104, 111, 117, 116, 32, 105, 109, 112, 111, 114, 116, 105, 110, 103, 32, 116, 104, 101, 32, 102, 105, 108, 101, 32, 116, 104, 101, 121, 10, 97, 114, 101, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 111, 110, 108, 121, 32, 117, 115, 101, 102, 117, 108, 32, 100, 117, 114, 105, 110, 103, 32, 98, 111, 111, 116, 115, 116, 114, 97, 112, 112, 105, 110, 103, 32, 97, 110, 100, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 117, 115, 101, 100, 32, 111, 117, 116, 115, 105, 100, 101, 32, 111, 102, 10, 116, 104, 101, 32, 76, 101, 97, 110, 32, 115, 111, 117, 114, 99, 101, 32, 99, 111, 100, 101, 46, 10, 0]};
static mut l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(
    mut v_declName_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: u8 = 0;
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_st_ref_get(v___y_443_);
    v_env_446_ = lean_ctor_get(v___x_445_, 0);
    lean_inc_ref(v_env_446_);
    lean_dec(v___x_445_);
    v___x_447_ = lean_st_ref_get(v___y_443_);
    v_env_448_ = lean_ctor_get(v___x_447_, 0);
    lean_inc_ref(v_env_448_);
    lean_dec(v___x_447_);
    v___x_449_ = l_Lean_declRangeExt;
    v_toEnvExtension_450_ = lean_ctor_get(v___x_449_, 0);
    v_asyncMode_451_ = lean_ctor_get(v_toEnvExtension_450_, 2);
    v___x_452_ = l_Lean_instInhabitedDeclarationRanges_default;
    v___x_453_ = 0;
    lean_inc(v_declName_442_);
    v___x_454_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_452_,
        v___x_449_,
        v_env_446_,
        v_declName_442_,
        v_asyncMode_451_,
        v___x_453_,
    );
    if lean_obj_tag(v___x_454_) == 0 {
        let mut v___x_455_: u8 = 0;
        let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
        v___x_455_ = 1;
        v___x_456_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
            v___x_452_,
            v___x_449_,
            v_env_448_,
            v_declName_442_,
            v_asyncMode_451_,
            v___x_455_,
        );
        v___x_457_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_457_, 0, v___x_456_);
        return v___x_457_;
    } else {
        let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_448_);
        lean_dec(v_declName_442_);
        v___x_458_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_458_, 0, v___x_454_);
        return v___x_458_;
    }
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg___boxed(
    mut v_declName_459_: *mut LeanObject,
    mut v___y_460_: *mut LeanObject,
    mut v___y_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_462_: *mut LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_459_, v___y_460_);
    lean_dec(v___y_460_);
    return v_res_462_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(
    mut v_declName_463_: *mut LeanObject,
    mut v___y_464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_466_ = lean_st_ref_get(v___y_464_);
    v_env_467_ = lean_ctor_get(v___x_466_, 0);
    lean_inc_ref(v_env_467_);
    lean_dec(v___x_466_);
    v___x_468_ = l_Lean_isRecCore(v_env_467_, v_declName_463_);
    v___x_469_ = lean_box((v___x_468_) as usize);
    v___x_470_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_470_, 0, v___x_469_);
    return v___x_470_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg___boxed(
    mut v_declName_471_: *mut LeanObject,
    mut v___y_472_: *mut LeanObject,
    mut v___y_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_474_: *mut LeanObject = core::ptr::null_mut();
    v_res_474_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_471_, v___y_472_);
    lean_dec(v___y_472_);
    return v_res_474_;
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(
    mut v_declName_475_: *mut LeanObject,
    mut v___y_476_: *mut LeanObject,
    mut v___y_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ranges_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_495_: u8 = 0;
    let mut v___x_496_: u8 = 0;
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: u8 = 0;
    let mut v___x_500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_486_ = lean_st_ref_get(v___y_477_);
                v_env_487_ = lean_ctor_get(v___x_486_, 0);
                lean_inc_ref_n(v_env_487_, 2);
                lean_dec(v___x_486_);
                lean_inc_n(v_declName_475_, 2);
                v___x_488_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_475_, v___y_477_);
                v_a_489_ = lean_ctor_get(v___x_488_, 0);
                lean_inc(v_a_489_);
                lean_dec_ref(v___x_488_);
                v___x_499_ = l_Lean_isAuxRecursor(v_env_487_, v_declName_475_);
                if v___x_499_ == 0 {
                    lean_inc(v_declName_475_);
                    v___x_500_ = l_Lean_isNoConfusion(v_env_487_, v_declName_475_);
                    v___y_495_ = v___x_500_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v_env_487_);
                    v___y_495_ = v___x_499_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_ranges_480_) == 0 {
                    v___x_481_ = l_Lean_builtinDeclRanges;
                    v___x_482_ = lean_st_ref_get(v___x_481_);
                    v___x_483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_482_, v_declName_475_);
                    lean_dec(v_declName_475_);
                    lean_dec(v___x_482_);
                    v___x_484_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_484_, 0, v___x_483_);
                    return v___x_484_;
                } else {
                    lean_dec(v_declName_475_);
                    v___x_485_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_485_, 0, v_ranges_480_);
                    return v___x_485_;
                }
            }
            2 => {
                v___x_491_ = l_Lean_Name_getPrefix(v_declName_475_);
                v___x_492_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v___x_491_, v___y_477_);
                v_a_493_ = lean_ctor_get(v___x_492_, 0);
                lean_inc(v_a_493_);
                lean_dec_ref(v___x_492_);
                v_ranges_480_ = v_a_493_;
                state = 1;
                continue;
            }
            3 => {
                if v___y_495_ == 0 {
                    v___x_496_ = (lean_unbox(v_a_489_) as u8);
                    lean_dec(v_a_489_);
                    if v___x_496_ == 0 {
                        lean_inc(v_declName_475_);
                        v___x_497_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_475_, v___y_477_);
                        v_a_498_ = lean_ctor_get(v___x_497_, 0);
                        lean_inc(v_a_498_);
                        lean_dec_ref(v___x_497_);
                        v_ranges_480_ = v_a_498_;
                        state = 1;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_489_);
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0___boxed(
    mut v_declName_501_: *mut LeanObject,
    mut v___y_502_: *mut LeanObject,
    mut v___y_503_: *mut LeanObject,
    mut v___y_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_505_: *mut LeanObject = core::ptr::null_mut();
    v_res_505_ =
        l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(
            v_declName_501_,
            v___y_502_,
            v___y_503_,
        );
    lean_dec(v___y_503_);
    lean_dec_ref(v___y_502_);
    return v_res_505_;
}
pub unsafe fn _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3() -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = lean_box(0);
    v___x_512_ = l_Lean_declareBuiltinDocStringAndRanges___closed__2;
    v___x_513_ = l_Lean_mkConst(v___x_512_, v___x_511_);
    return v___x_513_;
}
pub unsafe fn _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7() -> *mut LeanObject {
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    v___x_520_ = lean_box(0);
    v___x_521_ = l_Lean_declareBuiltinDocStringAndRanges___closed__6;
    v___x_522_ = l_Lean_mkConst(v___x_521_, v___x_520_);
    return v___x_522_;
}
pub unsafe fn _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10() -> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ = lean_box(0);
    v___x_529_ = l_Lean_declareBuiltinDocStringAndRanges___closed__9;
    v___x_530_ = l_Lean_mkConst(v___x_529_, v___x_528_);
    return v___x_530_;
}
pub unsafe fn _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13() -> *mut LeanObject {
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    v___x_536_ = lean_box(0);
    v___x_537_ = l_Lean_declareBuiltinDocStringAndRanges___closed__12;
    v___x_538_ = l_Lean_mkConst(v___x_537_, v___x_536_);
    return v___x_538_;
}
pub unsafe fn _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20() -> *mut LeanObject {
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    v___x_549_ = lean_box(0);
    v___x_550_ = l_Lean_declareBuiltinDocStringAndRanges___closed__19;
    v___x_551_ = l_Lean_mkConst(v___x_550_, v___x_549_);
    return v___x_551_;
}
pub unsafe fn l_Lean_declareBuiltinDocStringAndRanges(
    mut v_declName_552_: *mut LeanObject,
    mut v_a_553_: *mut LeanObject,
    mut v_a_554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_563_: u8 = 0;
    let mut v_val_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_selectionRange_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_column_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_639_: u8 = 0;
    let mut v_a_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_643_: u8 = 0;
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_653_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_a_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_668_: u8 = 0;
    let mut v_ref_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_648_ = lean_st_ref_get(v_a_554_);
                v_env_649_ = lean_ctor_get(v___x_648_, 0);
                lean_inc_ref(v_env_649_);
                lean_dec(v___x_648_);
                v___x_650_ = 0;
                lean_inc(v_declName_552_);
                v___x_651_ =
                    l_Lean_findSimpleDocString_x3f(v_env_649_, v_declName_552_, v___x_650_);
                if lean_obj_tag(v___x_651_) == 0 {
                    v_a_652_ = lean_ctor_get(v___x_651_, 0);
                    lean_inc(v_a_652_);
                    lean_dec_ref_known(v___x_651_, 1);
                    if lean_obj_tag(v_a_652_) == 1 {
                        v_val_653_ = lean_ctor_get(v_a_652_, 0);
                        lean_inc(v_val_653_);
                        lean_dec_ref_known(v_a_652_, 1);
                        v___x_654_ = l_Lean_declareBuiltinDocStringAndRanges___closed__17;
                        lean_inc_n(v_declName_552_, 2);
                        v___x_655_ = l_Lean_Name_append(v_declName_552_, v___x_654_);
                        v___x_656_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_declareBuiltinDocStringAndRanges___closed__20
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_declareBuiltinDocStringAndRanges___closed__20_once
                            ),
                            _init_l_Lean_declareBuiltinDocStringAndRanges___closed__20,
                        );
                        v___x_657_ =
                            l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_552_);
                        v___x_658_ = l_Lean_mkStrLit(v_val_653_);
                        v___x_659_ = lean_unsigned_to_nat(2);
                        v___x_660_ = lean_mk_empty_array_with_capacity(v___x_659_);
                        v___x_661_ = lean_array_push(v___x_660_, v___x_657_);
                        v___x_662_ = lean_array_push(v___x_661_, v___x_658_);
                        v___x_663_ = l_Lean_mkAppN(v___x_656_, v___x_662_);
                        lean_dec_ref(v___x_662_);
                        v___x_664_ =
                            l_Lean_declareBuiltin(v___x_655_, v___x_663_, v_a_553_, v_a_554_);
                        if lean_obj_tag(v___x_664_) == 0 {
                            lean_dec_ref_known(v___x_664_, 1);
                            v___y_557_ = v_a_553_;
                            v___y_558_ = v_a_554_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_declName_552_);
                            return v___x_664_;
                        }
                    } else {
                        lean_dec(v_a_652_);
                        v___y_557_ = v_a_553_;
                        v___y_558_ = v_a_554_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_552_);
                    v_a_665_ = lean_ctor_get(v___x_651_, 0);
                    v_isSharedCheck_677_ = (!lean_is_exclusive(v___x_651_)) as u8;
                    if v_isSharedCheck_677_ == 0 {
                        v___x_667_ = v___x_651_;
                        v_isShared_668_ = v_isSharedCheck_677_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_665_);
                        lean_dec(v___x_651_);
                        v___x_667_ = lean_box(0);
                        v_isShared_668_ = v_isSharedCheck_677_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_declName_552_);
                v___x_559_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0(v_declName_552_, v___y_557_, v___y_558_);
                if lean_obj_tag(v___x_559_) == 0 {
                    v_a_560_ = lean_ctor_get(v___x_559_, 0);
                    v_isSharedCheck_639_ = (!lean_is_exclusive(v___x_559_)) as u8;
                    if v_isSharedCheck_639_ == 0 {
                        v___x_562_ = v___x_559_;
                        v_isShared_563_ = v_isSharedCheck_639_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_560_);
                        lean_dec(v___x_559_);
                        v___x_562_ = lean_box(0);
                        v_isShared_563_ = v_isSharedCheck_639_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_552_);
                    v_a_640_ = lean_ctor_get(v___x_559_, 0);
                    v_isSharedCheck_647_ = (!lean_is_exclusive(v___x_559_)) as u8;
                    if v_isSharedCheck_647_ == 0 {
                        v___x_642_ = v___x_559_;
                        v_isShared_643_ = v_isSharedCheck_647_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_640_);
                        lean_dec(v___x_559_);
                        v___x_642_ = lean_box(0);
                        v_isShared_643_ = v_isSharedCheck_647_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_560_) == 1 {
                    lean_del_object(v___x_562_);
                    v_val_564_ = lean_ctor_get(v_a_560_, 0);
                    lean_inc(v_val_564_);
                    lean_dec_ref_known(v_a_560_, 1);
                    v_range_565_ = lean_ctor_get(v_val_564_, 0);
                    lean_inc_ref(v_range_565_);
                    v_pos_566_ = lean_ctor_get(v_range_565_, 0);
                    lean_inc_ref(v_pos_566_);
                    v_endPos_567_ = lean_ctor_get(v_range_565_, 2);
                    lean_inc_ref(v_endPos_567_);
                    v_selectionRange_568_ = lean_ctor_get(v_val_564_, 1);
                    lean_inc_ref(v_selectionRange_568_);
                    lean_dec(v_val_564_);
                    v_pos_569_ = lean_ctor_get(v_selectionRange_568_, 0);
                    lean_inc_ref(v_pos_569_);
                    v_charUtf16_570_ = lean_ctor_get(v_range_565_, 1);
                    lean_inc(v_charUtf16_570_);
                    v_endCharUtf16_571_ = lean_ctor_get(v_range_565_, 3);
                    lean_inc(v_endCharUtf16_571_);
                    lean_dec_ref(v_range_565_);
                    v_line_572_ = lean_ctor_get(v_pos_566_, 0);
                    lean_inc(v_line_572_);
                    v_column_573_ = lean_ctor_get(v_pos_566_, 1);
                    lean_inc(v_column_573_);
                    lean_dec_ref(v_pos_566_);
                    v_line_574_ = lean_ctor_get(v_endPos_567_, 0);
                    lean_inc(v_line_574_);
                    v_column_575_ = lean_ctor_get(v_endPos_567_, 1);
                    lean_inc(v_column_575_);
                    lean_dec_ref(v_endPos_567_);
                    v_charUtf16_576_ = lean_ctor_get(v_selectionRange_568_, 1);
                    lean_inc(v_charUtf16_576_);
                    v_endPos_577_ = lean_ctor_get(v_selectionRange_568_, 2);
                    lean_inc_ref(v_endPos_577_);
                    v_endCharUtf16_578_ = lean_ctor_get(v_selectionRange_568_, 3);
                    lean_inc(v_endCharUtf16_578_);
                    lean_dec_ref(v_selectionRange_568_);
                    v_line_579_ = lean_ctor_get(v_pos_569_, 0);
                    lean_inc(v_line_579_);
                    v_column_580_ = lean_ctor_get(v_pos_569_, 1);
                    lean_inc(v_column_580_);
                    lean_dec_ref(v_pos_569_);
                    v___x_581_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__3_once
                        ),
                        _init_l_Lean_declareBuiltinDocStringAndRanges___closed__3,
                    );
                    v_line_582_ = lean_ctor_get(v_endPos_577_, 0);
                    lean_inc(v_line_582_);
                    v_column_583_ = lean_ctor_get(v_endPos_577_, 1);
                    lean_inc(v_column_583_);
                    lean_dec_ref(v_endPos_577_);
                    v___x_584_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__7_once
                        ),
                        _init_l_Lean_declareBuiltinDocStringAndRanges___closed__7,
                    );
                    v___x_585_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__10_once
                        ),
                        _init_l_Lean_declareBuiltinDocStringAndRanges___closed__10,
                    );
                    v___x_586_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_declareBuiltinDocStringAndRanges___closed__13_once
                        ),
                        _init_l_Lean_declareBuiltinDocStringAndRanges___closed__13,
                    );
                    v___x_587_ = l_Lean_mkNatLit(v_line_572_);
                    v___x_588_ = l_Lean_mkNatLit(v_column_573_);
                    v___x_589_ = lean_unsigned_to_nat(2);
                    v___x_590_ = lean_mk_empty_array_with_capacity(v___x_589_);
                    lean_inc_ref_n(v___x_590_, 5);
                    v___x_591_ = lean_array_push(v___x_590_, v___x_587_);
                    v___x_592_ = lean_array_push(v___x_591_, v___x_588_);
                    v___x_593_ = l_Lean_mkAppN(v___x_586_, v___x_592_);
                    lean_dec_ref(v___x_592_);
                    v___x_594_ = l_Lean_declareBuiltinDocStringAndRanges___closed__15;
                    lean_inc(v_declName_552_);
                    v___x_595_ = l_Lean_Name_append(v_declName_552_, v___x_594_);
                    v___x_596_ = l_Lean_mkNatLit(v_line_574_);
                    v___x_597_ = l_Lean_mkNatLit(v_column_575_);
                    v___x_598_ = lean_array_push(v___x_590_, v___x_596_);
                    v___x_599_ = lean_array_push(v___x_598_, v___x_597_);
                    v___x_600_ = l_Lean_mkAppN(v___x_586_, v___x_599_);
                    lean_dec_ref(v___x_599_);
                    v___x_601_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_552_);
                    v___x_602_ = l_Lean_mkNatLit(v_charUtf16_570_);
                    v___x_603_ = l_Lean_mkNatLit(v_endCharUtf16_571_);
                    v___x_604_ = lean_unsigned_to_nat(4);
                    v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
                    lean_inc_ref(v___x_605_);
                    v___x_606_ = lean_array_push(v___x_605_, v___x_593_);
                    v___x_607_ = lean_array_push(v___x_606_, v___x_602_);
                    v___x_608_ = lean_array_push(v___x_607_, v___x_600_);
                    v___x_609_ = lean_array_push(v___x_608_, v___x_603_);
                    v___x_610_ = l_Lean_mkAppN(v___x_585_, v___x_609_);
                    lean_dec_ref(v___x_609_);
                    v___x_611_ = l_Lean_mkNatLit(v_line_579_);
                    v___x_612_ = l_Lean_mkNatLit(v_column_580_);
                    v___x_613_ = lean_array_push(v___x_590_, v___x_611_);
                    v___x_614_ = lean_array_push(v___x_613_, v___x_612_);
                    v___x_615_ = l_Lean_mkAppN(v___x_586_, v___x_614_);
                    lean_dec_ref(v___x_614_);
                    v___x_616_ = l_Lean_mkNatLit(v_charUtf16_576_);
                    v___x_617_ = l_Lean_mkNatLit(v_line_582_);
                    v___x_618_ = l_Lean_mkNatLit(v_column_583_);
                    v___x_619_ = lean_array_push(v___x_590_, v___x_617_);
                    v___x_620_ = lean_array_push(v___x_619_, v___x_618_);
                    v___x_621_ = l_Lean_mkAppN(v___x_586_, v___x_620_);
                    lean_dec_ref(v___x_620_);
                    v___x_622_ = l_Lean_mkNatLit(v_endCharUtf16_578_);
                    v___x_623_ = lean_array_push(v___x_605_, v___x_615_);
                    v___x_624_ = lean_array_push(v___x_623_, v___x_616_);
                    v___x_625_ = lean_array_push(v___x_624_, v___x_621_);
                    v___x_626_ = lean_array_push(v___x_625_, v___x_622_);
                    v___x_627_ = l_Lean_mkAppN(v___x_585_, v___x_626_);
                    lean_dec_ref(v___x_626_);
                    v___x_628_ = lean_array_push(v___x_590_, v___x_610_);
                    v___x_629_ = lean_array_push(v___x_628_, v___x_627_);
                    v___x_630_ = l_Lean_mkAppN(v___x_584_, v___x_629_);
                    lean_dec_ref(v___x_629_);
                    v___x_631_ = lean_array_push(v___x_590_, v___x_601_);
                    v___x_632_ = lean_array_push(v___x_631_, v___x_630_);
                    v___x_633_ = l_Lean_mkAppN(v___x_581_, v___x_632_);
                    lean_dec_ref(v___x_632_);
                    v___x_634_ =
                        l_Lean_declareBuiltin(v___x_595_, v___x_633_, v___y_557_, v___y_558_);
                    return v___x_634_;
                } else {
                    lean_dec(v_a_560_);
                    lean_dec(v_declName_552_);
                    v___x_635_ = lean_box(0);
                    if v_isShared_563_ == 0 {
                        lean_ctor_set(v___x_562_, 0, v___x_635_);
                        v___x_637_ = v___x_562_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
                        v___x_637_ = v_reuseFailAlloc_638_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_637_;
            }
            4 => {
                if v_isShared_643_ == 0 {
                    v___x_645_ = v___x_642_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
                    v___x_645_ = v_reuseFailAlloc_646_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_645_;
            }
            6 => {
                v_ref_669_ = lean_ctor_get(v_a_553_, 5);
                v___x_670_ = lean_io_error_to_string(v_a_665_);
                v___x_671_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_671_, 0, v___x_670_);
                v___x_672_ = l_Lean_MessageData_ofFormat(v___x_671_);
                lean_inc(v_ref_669_);
                v___x_673_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_673_, 0, v_ref_669_);
                lean_ctor_set(v___x_673_, 1, v___x_672_);
                if v_isShared_668_ == 0 {
                    lean_ctor_set(v___x_667_, 0, v___x_673_);
                    v___x_675_ = v___x_667_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
                    v___x_675_ = v_reuseFailAlloc_676_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_declareBuiltinDocStringAndRanges___boxed(
    mut v_declName_678_: *mut LeanObject,
    mut v_a_679_: *mut LeanObject,
    mut v_a_680_: *mut LeanObject,
    mut v_a_681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_682_: *mut LeanObject = core::ptr::null_mut();
    v_res_682_ = l_Lean_declareBuiltinDocStringAndRanges(v_declName_678_, v_a_679_, v_a_680_);
    lean_dec(v_a_680_);
    lean_dec_ref(v_a_679_);
    return v_res_682_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(
    mut v_declName_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
    mut v___y_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___redArg(v_declName_683_, v___y_685_);
    return v___x_687_;
}
pub unsafe fn l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0___boxed(
    mut v_declName_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_692_: *mut LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__0(v_declName_688_, v___y_689_, v___y_690_);
    lean_dec(v___y_690_);
    lean_dec_ref(v___y_689_);
    return v_res_692_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(
    mut v_declName_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___redArg(v_declName_693_, v___y_695_);
    return v___x_697_;
}
pub unsafe fn l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1___boxed(
    mut v_declName_698_: *mut LeanObject,
    mut v___y_699_: *mut LeanObject,
    mut v___y_700_: *mut LeanObject,
    mut v___y_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_702_: *mut LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_declareBuiltinDocStringAndRanges_spec__0_spec__1(v_declName_698_, v___y_699_, v___y_700_);
    lean_dec(v___y_700_);
    lean_dec_ref(v___y_699_);
    return v_res_702_;
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(
    mut v_decl_703_: *mut LeanObject,
    mut v_stx_704_: *mut LeanObject,
    mut v_x_705_: u8,
    mut v___y_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_704_, v___y_706_, v___y_707_);
    if lean_obj_tag(v___x_709_) == 0 {
        let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_709_, 1);
        v___x_710_ = l_Lean_declareBuiltinDocStringAndRanges(v_decl_703_, v___y_706_, v___y_707_);
        return v___x_710_;
    } else {
        lean_dec(v_decl_703_);
        return v___x_709_;
    }
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(
    mut v_decl_711_: *mut LeanObject,
    mut v_stx_712_: *mut LeanObject,
    mut v_x_713_: *mut LeanObject,
    mut v___y_714_: *mut LeanObject,
    mut v___y_715_: *mut LeanObject,
    mut v___y_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1051__boxed_717_: u8 = 0;
    let mut v_res_718_: *mut LeanObject = core::ptr::null_mut();
    v_x_1051__boxed_717_ = (lean_unbox(v_x_713_) as u8);
    v_res_718_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v_decl_711_, v_stx_712_, v_x_1051__boxed_717_, v___y_714_, v___y_715_);
    lean_dec(v___y_715_);
    lean_dec_ref(v___y_714_);
    return v_res_718_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_719_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_720_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_721_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_721_, 0, v___x_720_);
    return v___x_721_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    v___x_722_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_723_ = lean_unsigned_to_nat(0);
    v___x_724_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_724_, 0, v___x_723_);
    lean_ctor_set(v___x_724_, 1, v___x_723_);
    lean_ctor_set(v___x_724_, 2, v___x_723_);
    lean_ctor_set(v___x_724_, 3, v___x_723_);
    lean_ctor_set(v___x_724_, 4, v___x_722_);
    lean_ctor_set(v___x_724_, 5, v___x_722_);
    lean_ctor_set(v___x_724_, 6, v___x_722_);
    lean_ctor_set(v___x_724_, 7, v___x_722_);
    lean_ctor_set(v___x_724_, 8, v___x_722_);
    lean_ctor_set(v___x_724_, 9, v___x_722_);
    return v___x_724_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    v___x_725_ = lean_unsigned_to_nat(32);
    v___x_726_ = lean_mk_empty_array_with_capacity(v___x_725_);
    v___x_727_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_727_, 0, v___x_726_);
    return v___x_727_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_728_: usize = 0;
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    v___x_728_ = 5usize;
    v___x_729_ = lean_unsigned_to_nat(0);
    v___x_730_ = lean_unsigned_to_nat(32);
    v___x_731_ = lean_mk_empty_array_with_capacity(v___x_730_);
    v___x_732_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_733_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_733_, 0, v___x_732_);
    lean_ctor_set(v___x_733_, 1, v___x_731_);
    lean_ctor_set(v___x_733_, 2, v___x_729_);
    lean_ctor_set(v___x_733_, 3, v___x_729_);
    lean_ctor_set_usize(v___x_733_, 4, v___x_728_);
    return v___x_733_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    v___x_734_ = lean_box(1);
    v___x_735_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_736_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_737_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_737_, 0, v___x_736_);
    lean_ctor_set(v___x_737_, 1, v___x_735_);
    lean_ctor_set(v___x_737_, 2, v___x_734_);
    return v___x_737_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_738_: *mut LeanObject,
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_742_ = lean_st_ref_get(v___y_740_);
    v_env_743_ = lean_ctor_get(v___x_742_, 0);
    lean_inc_ref(v_env_743_);
    lean_dec(v___x_742_);
    v_options_744_ = lean_ctor_get(v___y_739_, 2);
    v___x_745_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_746_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_744_);
    v___x_747_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_747_, 0, v_env_743_);
    lean_ctor_set(v___x_747_, 1, v___x_745_);
    lean_ctor_set(v___x_747_, 2, v___x_746_);
    lean_ctor_set(v___x_747_, 3, v_options_744_);
    v___x_748_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_748_, 0, v___x_747_);
    lean_ctor_set(v___x_748_, 1, v_msgData_738_);
    v___x_749_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_749_, 0, v___x_748_);
    return v___x_749_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_750_: *mut LeanObject,
    mut v___y_751_: *mut LeanObject,
    mut v___y_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_754_: *mut LeanObject = core::ptr::null_mut();
    v_res_754_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msgData_750_, v___y_751_, v___y_752_);
    lean_dec(v___y_752_);
    lean_dec_ref(v___y_751_);
    return v_res_754_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_755_: *mut LeanObject,
    mut v___y_756_: *mut LeanObject,
    mut v___y_757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_759_ = lean_ctor_get(v___y_756_, 5);
                v___x_760_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0_spec__0(v_msg_755_, v___y_756_, v___y_757_);
                v_a_761_ = lean_ctor_get(v___x_760_, 0);
                v_isSharedCheck_769_ = (!lean_is_exclusive(v___x_760_)) as u8;
                if v_isSharedCheck_769_ == 0 {
                    v___x_763_ = v___x_760_;
                    v_isShared_764_ = v_isSharedCheck_769_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_761_);
                    lean_dec(v___x_760_);
                    v___x_763_ = lean_box(0);
                    v_isShared_764_ = v_isSharedCheck_769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_759_);
                v___x_765_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_765_, 0, v_ref_759_);
                lean_ctor_set(v___x_765_, 1, v_a_761_);
                if v_isShared_764_ == 0 {
                    lean_ctor_set_tag(v___x_763_, 1);
                    lean_ctor_set(v___x_763_, 0, v___x_765_);
                    v___x_767_ = v___x_763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
                    v___x_767_ = v_reuseFailAlloc_768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
    mut v___y_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_774_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_770_, v___y_771_, v___y_772_);
    lean_dec(v___y_772_);
    lean_dec_ref(v___y_771_);
    return v_res_774_;
}
pub unsafe fn _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_;
    v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
    return v___x_777_;
}
pub unsafe fn _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    v___x_779_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_;
    v___x_780_ = l_Lean_stringToMessageData(v___x_779_);
    return v___x_780_;
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(
    mut v___x_781_: *mut LeanObject,
    mut v_decl_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    v___x_786_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once), _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
    v___x_787_ = l_Lean_MessageData_ofName(v___x_781_);
    v___x_788_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_788_, 0, v___x_786_);
    lean_ctor_set(v___x_788_, 1, v___x_787_);
    v___x_789_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__once), _init_l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_);
    v___x_790_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_790_, 0, v___x_788_);
    lean_ctor_set(v___x_790_, 1, v___x_789_);
    v___x_791_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v___x_790_, v___y_783_, v___y_784_);
    return v___x_791_;
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(
    mut v___x_792_: *mut LeanObject,
    mut v_decl_793_: *mut LeanObject,
    mut v___y_794_: *mut LeanObject,
    mut v___y_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_797_: *mut LeanObject = core::ptr::null_mut();
    v_res_797_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___lam__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_(v___x_792_, v_decl_793_, v___y_794_, v___y_795_);
    lean_dec(v___y_795_);
    lean_dec_ref(v___y_794_);
    lean_dec(v_decl_793_);
    return v_res_797_;
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    v___x_860_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__25_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_;
    v___x_861_ = l_Lean_registerBuiltinAttribute(v___x_860_);
    return v___x_861_;
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(
    mut v_a_862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_863_: *mut LeanObject = core::ptr::null_mut();
    v_res_863_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
    return v_res_863_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_864_: *mut LeanObject,
    mut v_msg_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___redArg(v_msg_865_, v___y_866_, v___y_867_);
    return v___x_869_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_870_: *mut LeanObject,
    mut v_msg_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_875_: *mut LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Lean_throwError___at___00__private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2__spec__0(v_00_u03b1_870_, v_msg_871_, v___y_872_, v___y_873_);
    lean_dec(v___y_873_);
    lean_dec_ref(v___y_872_);
    return v_res_875_;
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_878_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___closed__19_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_;
    v___x_879_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_;
    v___x_880_ = l_Lean_addBuiltinDocString(v___x_878_, v___x_879_);
    return v___x_880_;
}
pub unsafe fn l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2____boxed(
    mut v_a_881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_882_: *mut LeanObject = core::ptr::null_mut();
    v_res_882_ = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
    return v_res_882_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_BuiltinDocAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_BuiltinDocAttr_0__Lean_initFn_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_BuiltinDocAttr_0__Lean_initFn___regBuiltin___private_Lean_BuiltinDocAttr_0__Lean_initFn_docString__1_00___x40_Lean_BuiltinDocAttr_939411776____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_BuiltinDocAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_BuiltinDocAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_BuiltinDocAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_BuiltinDocAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_BuiltinDocAttr(builtin);
}
