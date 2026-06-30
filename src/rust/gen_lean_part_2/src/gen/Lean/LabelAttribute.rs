// Lean compiler output
// Module: Lean.LabelAttribute
// Imports: Lean.DocString Init.Data.String.Extra Init.Data.ToString.Name
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_append, lean_string_intercalate, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_Array_eraseIdx___redArg, l_Array_instInhabited,
};
use crate::r#gen::Init::Data::String::Extra::{
    initialize_Init_Data_String_Extra, l_String_removeLeadingSpaces,
    runtime_initialize_Init_Data_String_Extra,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_Syntax_mkStrLit, l_Lean_TSyntax_getDocString, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom,
    l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_Lean_mkAtom, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DocString::{initialize_Lean_DocString, runtime_initialize_Lean_DocString};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addCore___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_ScopedEnvExtension_modifyState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
static mut l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_labelExtensionMapRef: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkLabelExt___auto__1___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_mkLabelExt___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__1_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_mkLabelExt___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__2_value: leanh::LeanStringObject<7> =
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
static mut l_Lean_mkLabelExt___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__3_value: leanh::LeanStringObject<10> =
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
static mut l_Lean_mkLabelExt___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_mkLabelExt___auto__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_mkLabelExt___auto__1___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__3_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__5_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_mkLabelExt___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__6_value: leanh::LeanStringObject<19> =
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
static mut l_Lean_mkLabelExt___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_mkLabelExt___auto__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_mkLabelExt___auto__1___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__6_value)
                as *mut leanh::LeanObject,
            17228437386856258271 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_mkLabelExt___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__9_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__10_value: leanh::LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_mkLabelExt___auto__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_mkLabelExt___auto__1___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__10_value)
                as *mut leanh::LeanObject,
            14997215300048349804 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkLabelExt___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkLabelExt___auto__1___closed__14_value: leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__15_value: leanh::LeanStringObject<9> =
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
        m_data: [100, 101, 99, 108, 78, 97, 109, 101, 0],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_mkLabelExt___auto__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_mkLabelExt___auto__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_mkLabelExt___auto__1___closed__16_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__16_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__15_value)
                as *mut leanh::LeanObject,
            7677164612348466033 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___auto__1___closed__17_value: leanh::LeanStringObject<11> =
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
        m_data: [100, 101, 99, 108, 95, 110, 97, 109, 101, 37, 0],
    };
static mut l_Lean_mkLabelExt___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkLabelExt___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkLabelExt___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelExt___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_mkLabelExt___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkLabelExt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkLabelExt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkLabelExt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkLabelExt___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkLabelExt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_mkLabelExt___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_mkLabelExt___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_mkLabelExt___closed__3_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_mkLabelExt___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkLabelExt___closed__3_value) as *mut leanh::LeanObject;
pub static mut l_Lean_mkLabelAttr___auto__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkLabelAttr___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkLabelAttr___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_registerLabelAttr___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0: u64 = 0;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__0_value:
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
    m_data: [95, 114, 111, 111, 116, 95, 0],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__1_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__2_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 76, 97, 98, 101, 108, 65, 116, 116, 114, 0,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__0_value)
            as *mut leanh::LeanObject,
        10026706816877452169 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        5582271100535066060 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        17028050061511929621 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__1_value)
            as *mut leanh::LeanObject,
        3041133114796605820 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Parser_Command_registerLabelAttr___closed__3_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__3_value_aux_4)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__2_value)
            as *mut leanh::LeanObject,
        2760989291541838557 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__4_value:
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
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__5_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__4_value)
            as *mut leanh::LeanObject,
        12571085391447129896 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__6_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__7_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__6_value)
            as *mut leanh::LeanObject,
        18170484695678750185 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__8_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__9_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__8_value)
            as *mut leanh::LeanObject,
        3961966953292576997 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__12_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
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
        114, 101, 103, 105, 115, 116, 101, 114, 95, 108, 97, 98, 101, 108, 95, 97, 116, 116, 114,
        32, 0,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__14_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__15_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__15_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__16_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__18_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__14_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__17_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Parser_Command_registerLabelAttr___closed__19_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__3_value)
            as *mut leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Command_registerLabelAttr___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__19_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Parser_Command_registerLabelAttr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 121, 110, 116, 97, 120, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__1_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0_value) as *mut leanh::LeanObject,2812521669163367463 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__1_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__3_value) as *mut leanh::LeanObject,17682753938374962505 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 111, 109, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__9_value) as *mut leanh::LeanObject,1765827125244227832 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__10_value) as *mut leanh::LeanObject,6376237424612349584 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 116, 114, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12_value) as *mut leanh::LeanObject,6289677862665402693 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 75, 101, 121, 119, 111, 114, 100, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__1_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__15_value) as *mut leanh::LeanObject,387456110215466097 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 120, 116, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17_value) as *mut leanh::LeanObject,6455343056875556081 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__20_value) as *mut leanh::LeanObject,4498178684837002829 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [76, 101, 97, 110, 46, 76, 97, 98, 101, 108, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 97, 98, 101, 108, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__25_value) as *mut leanh::LeanObject,15583760460604004565 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__27_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 134, 144, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__30_value) as *mut leanh::LeanObject,3326968124746134365 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__32_value) as *mut leanh::LeanObject,940684074193935882 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__34_value) as *mut leanh::LeanObject,5573444893818005634 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__36_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__2_value) as *mut leanh::LeanObject,9287336385012611462 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__2_value) as *mut leanh::LeanObject,8357017805368977423 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__40_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__41_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__14_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__43_value) as *mut leanh::LeanObject,9368229134555052249 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__1_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47_value) as *mut leanh::LeanObject,12014440461648055863 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Command_registerLabelAttr___closed__1_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__49_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50_value) as *mut leanh::LeanObject;
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52_value) as *mut leanh::LeanObject;
static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkLabelExt___auto__1___closed__1_value) as *mut leanh::LeanObject,6907480769838958894 as *mut leanh::LeanObject] };
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__52_value) as *mut leanh::LeanObject,16282038225239345418 as *mut leanh::LeanObject] };
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53_value) as *mut leanh::LeanObject;
pub static l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [108, 97, 98, 101, 108, 108, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 0]};
static mut l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_labelled___closed__0_value: leanh::LeanStringObject<20> =
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
            78, 111, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 32, 110, 97, 109, 101, 100,
            32, 0,
        ],
    };
static mut l_Lean_labelled___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_labelled___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_labelled___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_labelled___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = leanh::lean_box(0);
    v___x_1046_ = leanh::lean_unsigned_to_nat(16);
    v___x_1047_ = lean_mk_array(v___x_1046_, v___x_1045_);
    return v___x_1047_;
}
pub unsafe fn _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once), _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__0_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_);
    v___x_1049_ = leanh::lean_unsigned_to_nat(0);
    v___x_1050_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1050_, 0, v___x_1049_);
    leanh::lean_ctor_set(v___x_1050_, 1, v___x_1048_);
    return v___x_1050_;
}
pub unsafe fn l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2__once), _init_l___private_Lean_LabelAttribute_0__Lean_initFn___closed__1_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_);
    v___x_1053_ = lean_st_mk_ref(v___x_1052_);
    v___x_1054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1054_, 0, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2____boxed(
    mut v_a_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_();
    return v_res_1056_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lean_mkLabelExt___auto__1___closed__10;
    v___x_1084_ = l_Lean_mkAtom(v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__12_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__12,
    );
    v___x_1086_ = l_Lean_mkLabelExt___auto__1___closed__5;
    v___x_1087_ = lean_array_push(v___x_1086_, v___x_1085_);
    return v___x_1087_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1096_ = l_Lean_mkLabelExt___auto__1___closed__17;
    v___x_1097_ = l_Lean_mkAtom(v___x_1096_);
    return v___x_1097_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__19() -> *mut leanh::LeanObject {
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__18_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__18,
    );
    v___x_1099_ = l_Lean_mkLabelExt___auto__1___closed__5;
    v___x_1100_ = lean_array_push(v___x_1099_, v___x_1098_);
    return v___x_1100_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__20() -> *mut leanh::LeanObject {
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__19_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__19,
    );
    v___x_1102_ = l_Lean_mkLabelExt___auto__1___closed__16;
    v___x_1103_ = leanh::lean_box(2);
    v___x_1104_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    leanh::lean_ctor_set(v___x_1104_, 1, v___x_1102_);
    leanh::lean_ctor_set(v___x_1104_, 2, v___x_1101_);
    return v___x_1104_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__20_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__20,
    );
    v___x_1106_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__13_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__13,
    );
    v___x_1107_ = lean_array_push(v___x_1106_, v___x_1105_);
    return v___x_1107_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__22() -> *mut leanh::LeanObject {
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__21_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__21,
    );
    v___x_1109_ = l_Lean_mkLabelExt___auto__1___closed__11;
    v___x_1110_ = leanh::lean_box(2);
    v___x_1111_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1111_, 0, v___x_1110_);
    leanh::lean_ctor_set(v___x_1111_, 1, v___x_1109_);
    leanh::lean_ctor_set(v___x_1111_, 2, v___x_1108_);
    return v___x_1111_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__23() -> *mut leanh::LeanObject {
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__22_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__22,
    );
    v___x_1113_ = l_Lean_mkLabelExt___auto__1___closed__5;
    v___x_1114_ = lean_array_push(v___x_1113_, v___x_1112_);
    return v___x_1114_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__23_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__23,
    );
    v___x_1116_ = l_Lean_mkLabelExt___auto__1___closed__9;
    v___x_1117_ = leanh::lean_box(2);
    v___x_1118_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1118_, 0, v___x_1117_);
    leanh::lean_ctor_set(v___x_1118_, 1, v___x_1116_);
    leanh::lean_ctor_set(v___x_1118_, 2, v___x_1115_);
    return v___x_1118_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__25() -> *mut leanh::LeanObject {
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__24_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__24,
    );
    v___x_1120_ = l_Lean_mkLabelExt___auto__1___closed__5;
    v___x_1121_ = lean_array_push(v___x_1120_, v___x_1119_);
    return v___x_1121_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__26() -> *mut leanh::LeanObject {
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__25_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__25,
    );
    v___x_1123_ = l_Lean_mkLabelExt___auto__1___closed__7;
    v___x_1124_ = leanh::lean_box(2);
    v___x_1125_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1125_, 0, v___x_1124_);
    leanh::lean_ctor_set(v___x_1125_, 1, v___x_1123_);
    leanh::lean_ctor_set(v___x_1125_, 2, v___x_1122_);
    return v___x_1125_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__26_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__26,
    );
    v___x_1127_ = l_Lean_mkLabelExt___auto__1___closed__5;
    v___x_1128_ = lean_array_push(v___x_1127_, v___x_1126_);
    return v___x_1128_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1___closed__28() -> *mut leanh::LeanObject {
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__27_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__27,
    );
    v___x_1130_ = l_Lean_mkLabelExt___auto__1___closed__4;
    v___x_1131_ = leanh::lean_box(2);
    v___x_1132_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1132_, 0, v___x_1131_);
    leanh::lean_ctor_set(v___x_1132_, 1, v___x_1130_);
    leanh::lean_ctor_set(v___x_1132_, 2, v___x_1129_);
    return v___x_1132_;
}
pub unsafe fn _init_l_Lean_mkLabelExt___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__28_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__28,
    );
    return v___x_1133_;
}
pub unsafe fn l_Lean_mkLabelExt___lam__0(
    mut v_x_1134_: *mut leanh::LeanObject,
    mut v_a_1135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1136_, 0, v_a_1135_);
    leanh::lean_inc_ref_n(v___x_1136_, 2);
    v___x_1137_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1137_, 0, v___x_1136_);
    leanh::lean_ctor_set(v___x_1137_, 1, v___x_1136_);
    leanh::lean_ctor_set(v___x_1137_, 2, v___x_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_mkLabelExt___lam__0___boxed(
    mut v_x_1138_: *mut leanh::LeanObject,
    mut v_a_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_Lean_mkLabelExt___lam__0(v_x_1138_, v_a_1139_);
    leanh::lean_dec_ref(v_x_1138_);
    return v_res_1140_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(
    mut v_a_1141_: *mut leanh::LeanObject,
    mut v_as_1142_: *mut leanh::LeanObject,
    mut v_i_1143_: usize,
    mut v_stop_1144_: usize,
) -> u8 {
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: usize = 0;
    let mut v___x_1149_: usize = 0;
    let mut v___x_1151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1145_ = lean_usize_dec_eq(v_i_1143_, v_stop_1144_);
                if v___x_1145_ == 0 {
                    v___x_1146_ = lean_array_uget_borrowed(v_as_1142_, v_i_1143_);
                    v___x_1147_ = lean_name_eq(v_a_1141_, v___x_1146_);
                    if v___x_1147_ == 0 {
                        v___x_1148_ = 1usize;
                        v___x_1149_ = lean_usize_add(v_i_1143_, v___x_1148_);
                        v_i_1143_ = v___x_1149_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1147_;
                    }
                } else {
                    v___x_1151_ = 0;
                    return v___x_1151_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0___boxed(
    mut v_a_1152_: *mut leanh::LeanObject,
    mut v_as_1153_: *mut leanh::LeanObject,
    mut v_i_1154_: *mut leanh::LeanObject,
    mut v_stop_1155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1156_: usize = 0;
    let mut v_stop_boxed_1157_: usize = 0;
    let mut v_res_1158_: u8 = 0;
    let mut v_r_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1156_ = leanh::lean_unbox_usize(v_i_1154_);
    leanh::lean_dec(v_i_1154_);
    v_stop_boxed_1157_ = leanh::lean_unbox_usize(v_stop_1155_);
    leanh::lean_dec(v_stop_1155_);
    v_res_1158_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_1152_, v_as_1153_, v_i_boxed_1156_, v_stop_boxed_1157_);
    leanh::lean_dec_ref(v_as_1153_);
    leanh::lean_dec(v_a_1152_);
    v_r_1159_ = leanh::lean_box((v_res_1158_) as usize);
    return v_r_1159_;
}
pub unsafe fn l_Array_contains___at___00Lean_mkLabelExt_spec__0(
    mut v_as_1160_: *mut leanh::LeanObject,
    mut v_a_1161_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: u8 = 0;
    v___x_1162_ = leanh::lean_unsigned_to_nat(0);
    v___x_1163_ = lean_array_get_size(v_as_1160_);
    v___x_1164_ = lean_nat_dec_lt(v___x_1162_, v___x_1163_);
    if v___x_1164_ == 0 {
        return v___x_1164_;
    } else {
        if v___x_1164_ == 0 {
            return v___x_1164_;
        } else {
            let mut v___x_1165_: usize = 0;
            let mut v___x_1166_: usize = 0;
            let mut v___x_1167_: u8 = 0;
            v___x_1165_ = 0usize;
            v___x_1166_ = lean_usize_of_nat(v___x_1163_);
            v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mkLabelExt_spec__0_spec__0(v_a_1161_, v_as_1160_, v___x_1165_, v___x_1166_);
            return v___x_1167_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_mkLabelExt_spec__0___boxed(
    mut v_as_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1170_: u8 = 0;
    let mut v_r_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_as_1168_, v_a_1169_);
    leanh::lean_dec(v_a_1169_);
    leanh::lean_dec_ref(v_as_1168_);
    v_r_1171_ = leanh::lean_box((v_res_1170_) as usize);
    return v_r_1171_;
}
pub unsafe fn l_Lean_mkLabelExt___lam__1(
    mut v_d_1172_: *mut leanh::LeanObject,
    mut v_e_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1174_: u8 = 0;
    v___x_1174_ = l_Array_contains___at___00Lean_mkLabelExt_spec__0(v_d_1172_, v_e_1173_);
    if v___x_1174_ == 0 {
        let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1175_ = lean_array_push(v_d_1172_, v_e_1173_);
        return v___x_1175_;
    } else {
        leanh::lean_dec(v_e_1173_);
        return v_d_1172_;
    }
}
pub unsafe fn l_Lean_mkLabelExt___lam__2(
    mut v___y_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_1176_);
    return v___y_1176_;
}
pub unsafe fn l_Lean_mkLabelExt___lam__2___boxed(
    mut v___y_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Lean_mkLabelExt___lam__2(v___y_1177_);
    leanh::lean_dec_ref(v___y_1177_);
    return v_res_1178_;
}
pub unsafe fn l_Lean_mkLabelExt(
    mut v_name_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1186_ = l_Lean_mkLabelExt___closed__0;
    v___f_1187_ = l_Lean_mkLabelExt___closed__1;
    v___f_1188_ = l_Lean_mkLabelExt___closed__2;
    v___x_1189_ = l_Lean_mkLabelExt___closed__3;
    v___x_1190_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1190_, 0, v_name_1184_);
    leanh::lean_ctor_set(v___x_1190_, 1, v___f_1187_);
    leanh::lean_ctor_set(v___x_1190_, 2, v___x_1189_);
    leanh::lean_ctor_set(v___x_1190_, 3, v___f_1188_);
    leanh::lean_ctor_set(v___x_1190_, 4, v___f_1186_);
    v___x_1191_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Lean_mkLabelExt___boxed(
    mut v_name_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Lean_mkLabelExt(v_name_1192_);
    return v_res_1194_;
}
pub unsafe fn _init_l_Lean_mkLabelAttr___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__28_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__28,
    );
    return v___x_1195_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1196_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1196_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__0);
    v___x_1198_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1198_, 0, v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1199_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__1);
    v___x_1200_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1200_, 0, v___x_1199_);
    leanh::lean_ctor_set(v___x_1200_, 1, v___x_1199_);
    return v___x_1200_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(
    mut v_ext_1201_: *mut leanh::LeanObject,
    mut v_b_1202_: *mut leanh::LeanObject,
    mut v_kind_1203_: u8,
    mut v___y_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_currNamespace_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut v_unused_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_1207_ = leanh::lean_ctor_get(v___y_1204_, 6);
                v___x_1208_ = lean_st_ref_take(v___y_1205_);
                v_env_1209_ = leanh::lean_ctor_get(v___x_1208_, 0);
                v_nextMacroScope_1210_ = leanh::lean_ctor_get(v___x_1208_, 1);
                v_ngen_1211_ = leanh::lean_ctor_get(v___x_1208_, 2);
                v_auxDeclNGen_1212_ = leanh::lean_ctor_get(v___x_1208_, 3);
                v_traceState_1213_ = leanh::lean_ctor_get(v___x_1208_, 4);
                v_messages_1214_ = leanh::lean_ctor_get(v___x_1208_, 6);
                v_infoState_1215_ = leanh::lean_ctor_get(v___x_1208_, 7);
                v_snapshotTasks_1216_ = leanh::lean_ctor_get(v___x_1208_, 8);
                v_isSharedCheck_1228_ = (!leanh::lean_is_exclusive(v___x_1208_)) as u8;
                if v_isSharedCheck_1228_ == 0 {
                    v_unused_1229_ = leanh::lean_ctor_get(v___x_1208_, 5);
                    leanh::lean_dec(v_unused_1229_);
                    v___x_1218_ = v___x_1208_;
                    v_isShared_1219_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1216_);
                    leanh::lean_inc(v_infoState_1215_);
                    leanh::lean_inc(v_messages_1214_);
                    leanh::lean_inc(v_traceState_1213_);
                    leanh::lean_inc(v_auxDeclNGen_1212_);
                    leanh::lean_inc(v_ngen_1211_);
                    leanh::lean_inc(v_nextMacroScope_1210_);
                    leanh::lean_inc(v_env_1209_);
                    leanh::lean_dec(v___x_1208_);
                    v___x_1218_ = leanh::lean_box(0);
                    v_isShared_1219_ = v_isSharedCheck_1228_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_currNamespace_1207_);
                v___x_1220_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_1209_,
                    v_ext_1201_,
                    v_b_1202_,
                    v_kind_1203_,
                    v_currNamespace_1207_,
                );
                v___x_1221_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
                if v_isShared_1219_ == 0 {
                    leanh::lean_ctor_set(v___x_1218_, 5, v___x_1221_);
                    leanh::lean_ctor_set(v___x_1218_, 0, v___x_1220_);
                    v___x_1223_ = v___x_1218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_nextMacroScope_1210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 2, v_ngen_1211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 3, v_auxDeclNGen_1212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 4, v_traceState_1213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 5, v___x_1221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 6, v_messages_1214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 7, v_infoState_1215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1227_, 8, v_snapshotTasks_1216_);
                    v___x_1223_ = v_reuseFailAlloc_1227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1224_ = lean_st_ref_set(v___y_1205_, v___x_1223_);
                v___x_1225_ = leanh::lean_box(0);
                v___x_1226_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1226_, 0, v___x_1225_);
                return v___x_1226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___boxed(
    mut v_ext_1230_: *mut leanh::LeanObject,
    mut v_b_1231_: *mut leanh::LeanObject,
    mut v_kind_1232_: *mut leanh::LeanObject,
    mut v___y_1233_: *mut leanh::LeanObject,
    mut v___y_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1236_: u8 = 0;
    let mut v_res_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1236_ = (leanh::lean_unbox(v_kind_1232_) as u8);
    v_res_1237_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(
        v_ext_1230_,
        v_b_1231_,
        v_kind_boxed_1236_,
        v___y_1233_,
        v___y_1234_,
    );
    leanh::lean_dec(v___y_1234_);
    leanh::lean_dec_ref(v___y_1233_);
    return v_res_1237_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(
    mut v_00_u03b1_1238_: *mut leanh::LeanObject,
    mut v_00_u03b2_1239_: *mut leanh::LeanObject,
    mut v_00_u03c3_1240_: *mut leanh::LeanObject,
    mut v_ext_1241_: *mut leanh::LeanObject,
    mut v_b_1242_: *mut leanh::LeanObject,
    mut v_kind_1243_: u8,
    mut v___y_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(
        v_ext_1241_,
        v_b_1242_,
        v_kind_1243_,
        v___y_1244_,
        v___y_1245_,
    );
    return v___x_1247_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___boxed(
    mut v_00_u03b1_1248_: *mut leanh::LeanObject,
    mut v_00_u03b2_1249_: *mut leanh::LeanObject,
    mut v_00_u03c3_1250_: *mut leanh::LeanObject,
    mut v_ext_1251_: *mut leanh::LeanObject,
    mut v_b_1252_: *mut leanh::LeanObject,
    mut v_kind_1253_: *mut leanh::LeanObject,
    mut v___y_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1257_: u8 = 0;
    let mut v_res_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1257_ = (leanh::lean_unbox(v_kind_1253_) as u8);
    v_res_1258_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0(
        v_00_u03b1_1248_,
        v_00_u03b2_1249_,
        v_00_u03c3_1250_,
        v_ext_1251_,
        v_b_1252_,
        v_kind_boxed_1257_,
        v___y_1254_,
        v___y_1255_,
    );
    leanh::lean_dec(v___y_1255_);
    leanh::lean_dec_ref(v___y_1254_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_mkLabelAttr___lam__0(
    mut v_ext_1259_: *mut leanh::LeanObject,
    mut v_declName_1260_: *mut leanh::LeanObject,
    mut v_x_1261_: *mut leanh::LeanObject,
    mut v_kind_1262_: u8,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg(
        v_ext_1259_,
        v_declName_1260_,
        v_kind_1262_,
        v___y_1263_,
        v___y_1264_,
    );
    return v___x_1266_;
}
pub unsafe fn l_Lean_mkLabelAttr___lam__0___boxed(
    mut v_ext_1267_: *mut leanh::LeanObject,
    mut v_declName_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
    mut v_kind_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_1274_: u8 = 0;
    let mut v_res_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1274_ = (leanh::lean_unbox(v_kind_1270_) as u8);
    v_res_1275_ = l_Lean_mkLabelAttr___lam__0(
        v_ext_1267_,
        v_declName_1268_,
        v_x_1269_,
        v_kind_boxed_1274_,
        v___y_1271_,
        v___y_1272_,
    );
    leanh::lean_dec(v___y_1272_);
    leanh::lean_dec_ref(v___y_1271_);
    leanh::lean_dec(v_x_1269_);
    return v_res_1275_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(
    mut v_xs_1276_: *mut leanh::LeanObject,
    mut v_v_1277_: *mut leanh::LeanObject,
    mut v_i_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u8 = 0;
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: u8 = 0;
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1279_ = lean_array_get_size(v_xs_1276_);
                v___x_1280_ = lean_nat_dec_lt(v_i_1278_, v___x_1279_);
                if v___x_1280_ == 0 {
                    leanh::lean_dec(v_i_1278_);
                    v___x_1281_ = leanh::lean_box(0);
                    return v___x_1281_;
                } else {
                    v___x_1282_ = lean_array_fget_borrowed(v_xs_1276_, v_i_1278_);
                    v___x_1283_ = lean_name_eq(v___x_1282_, v_v_1277_);
                    if v___x_1283_ == 0 {
                        v___x_1284_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1285_ = lean_nat_add(v_i_1278_, v___x_1284_);
                        leanh::lean_dec(v_i_1278_);
                        v_i_1278_ = v___x_1285_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1287_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1287_, 0, v_i_1278_);
                        return v___x_1287_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2___boxed(
    mut v_xs_1288_: *mut leanh::LeanObject,
    mut v_v_1289_: *mut leanh::LeanObject,
    mut v_i_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_1288_, v_v_1289_, v_i_1290_);
    leanh::lean_dec(v_v_1289_);
    leanh::lean_dec_ref(v_xs_1288_);
    return v_res_1291_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(
    mut v_xs_1292_: *mut leanh::LeanObject,
    mut v_v_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = leanh::lean_unsigned_to_nat(0);
    v___x_1295_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1_spec__2(v_xs_1292_, v_v_1293_, v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1___boxed(
    mut v_xs_1296_: *mut leanh::LeanObject,
    mut v_v_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1298_ =
        l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(
            v_xs_1296_, v_v_1297_,
        );
    leanh::lean_dec(v_v_1297_);
    leanh::lean_dec_ref(v_xs_1296_);
    return v_res_1298_;
}
pub unsafe fn l_Array_erase___at___00Lean_mkLabelAttr_spec__1(
    mut v_as_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1301_ =
        l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_mkLabelAttr_spec__1_spec__1(
            v_as_1299_, v_a_1300_,
        );
    if leanh::lean_obj_tag(v___x_1301_) == 0 {
        return v_as_1299_;
    } else {
        let mut v_val_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1302_ = leanh::lean_ctor_get(v___x_1301_, 0);
        leanh::lean_inc(v_val_1302_);
        leanh::lean_dec_ref_known(v___x_1301_, 1);
        v___x_1303_ = l_Array_eraseIdx___redArg(v_as_1299_, v_val_1302_);
        return v___x_1303_;
    }
}
pub unsafe fn l_Array_erase___at___00Lean_mkLabelAttr_spec__1___boxed(
    mut v_as_1304_: *mut leanh::LeanObject,
    mut v_a_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v_as_1304_, v_a_1305_);
    leanh::lean_dec(v_a_1305_);
    return v_res_1306_;
}
pub unsafe fn l_Lean_mkLabelAttr___lam__1(
    mut v___x_1307_: *mut leanh::LeanObject,
    mut v_declName_1308_: *mut leanh::LeanObject,
    mut v_x_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1310_ = l_Array_erase___at___00Lean_mkLabelAttr_spec__1(v___x_1307_, v_declName_1308_);
    return v___x_1310_;
}
pub unsafe fn l_Lean_mkLabelAttr___lam__1___boxed(
    mut v___x_1311_: *mut leanh::LeanObject,
    mut v_declName_1312_: *mut leanh::LeanObject,
    mut v_x_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Lean_mkLabelAttr___lam__1(v___x_1311_, v_declName_1312_, v_x_1313_);
    leanh::lean_dec_ref(v_x_1313_);
    leanh::lean_dec(v_declName_1312_);
    return v_res_1314_;
}
pub unsafe fn l_Lean_mkLabelAttr___lam__2(
    mut v_ext_1315_: *mut leanh::LeanObject,
    mut v___x_1316_: *mut leanh::LeanObject,
    mut v_declName_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1348_: u8 = 0;
    let mut v_unused_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1321_ = lean_st_ref_get(v___y_1319_);
                v___x_1322_ = lean_st_ref_take(v___y_1319_);
                v_ext_1323_ = leanh::lean_ctor_get(v_ext_1315_, 1);
                v_toEnvExtension_1324_ = leanh::lean_ctor_get(v_ext_1323_, 0);
                v_env_1325_ = leanh::lean_ctor_get(v___x_1321_, 0);
                leanh::lean_inc_ref(v_env_1325_);
                leanh::lean_dec(v___x_1321_);
                v_asyncMode_1326_ = leanh::lean_ctor_get(v_toEnvExtension_1324_, 2);
                v_env_1327_ = leanh::lean_ctor_get(v___x_1322_, 0);
                v_nextMacroScope_1328_ = leanh::lean_ctor_get(v___x_1322_, 1);
                v_ngen_1329_ = leanh::lean_ctor_get(v___x_1322_, 2);
                v_auxDeclNGen_1330_ = leanh::lean_ctor_get(v___x_1322_, 3);
                v_traceState_1331_ = leanh::lean_ctor_get(v___x_1322_, 4);
                v_messages_1332_ = leanh::lean_ctor_get(v___x_1322_, 6);
                v_infoState_1333_ = leanh::lean_ctor_get(v___x_1322_, 7);
                v_snapshotTasks_1334_ = leanh::lean_ctor_get(v___x_1322_, 8);
                v_isSharedCheck_1348_ = (!leanh::lean_is_exclusive(v___x_1322_)) as u8;
                if v_isSharedCheck_1348_ == 0 {
                    v_unused_1349_ = leanh::lean_ctor_get(v___x_1322_, 5);
                    leanh::lean_dec(v_unused_1349_);
                    v___x_1336_ = v___x_1322_;
                    v_isShared_1337_ = v_isSharedCheck_1348_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1334_);
                    leanh::lean_inc(v_infoState_1333_);
                    leanh::lean_inc(v_messages_1332_);
                    leanh::lean_inc(v_traceState_1331_);
                    leanh::lean_inc(v_auxDeclNGen_1330_);
                    leanh::lean_inc(v_ngen_1329_);
                    leanh::lean_inc(v_nextMacroScope_1328_);
                    leanh::lean_inc(v_env_1327_);
                    leanh::lean_dec(v___x_1322_);
                    v___x_1336_ = leanh::lean_box(0);
                    v_isShared_1337_ = v_isSharedCheck_1348_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1338_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_1316_,
                    v_ext_1315_,
                    v_env_1325_,
                    v_asyncMode_1326_,
                );
                v___f_1339_ = leanh::lean_alloc_closure(
                    l_Lean_mkLabelAttr___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1339_, 0, v___x_1338_);
                leanh::lean_closure_set(v___f_1339_, 1, v_declName_1317_);
                v___x_1340_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v_ext_1315_,
                    v_env_1327_,
                    v___f_1339_,
                );
                v___x_1341_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_mkLabelAttr_spec__0___redArg___closed__2);
                if v_isShared_1337_ == 0 {
                    leanh::lean_ctor_set(v___x_1336_, 5, v___x_1341_);
                    leanh::lean_ctor_set(v___x_1336_, 0, v___x_1340_);
                    v___x_1343_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1347_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_nextMacroScope_1328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_ngen_1329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_auxDeclNGen_1330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_traceState_1331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 5, v___x_1341_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 6, v_messages_1332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 7, v_infoState_1333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1347_, 8, v_snapshotTasks_1334_);
                    v___x_1343_ = v_reuseFailAlloc_1347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1344_ = lean_st_ref_set(v___y_1319_, v___x_1343_);
                v___x_1345_ = leanh::lean_box(0);
                v___x_1346_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1346_, 0, v___x_1345_);
                return v___x_1346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkLabelAttr___lam__2___boxed(
    mut v_ext_1350_: *mut leanh::LeanObject,
    mut v___x_1351_: *mut leanh::LeanObject,
    mut v_declName_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_Lean_mkLabelAttr___lam__2(
        v_ext_1350_,
        v___x_1351_,
        v_declName_1352_,
        v___y_1353_,
        v___y_1354_,
    );
    leanh::lean_dec(v___y_1354_);
    leanh::lean_dec_ref(v___y_1353_);
    leanh::lean_dec_ref(v___x_1351_);
    return v_res_1356_;
}
pub unsafe fn _init_l_Lean_mkLabelAttr___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_1357_;
}
pub unsafe fn l_Lean_mkLabelAttr(
    mut v_attrName_1358_: *mut leanh::LeanObject,
    mut v_attrDescr_1359_: *mut leanh::LeanObject,
    mut v_ext_1360_: *mut leanh::LeanObject,
    mut v_ref_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: u8 = 0;
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_ext_1360_);
    v___f_1363_ = leanh::lean_alloc_closure(
        l_Lean_mkLabelAttr___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_1363_, 0, v_ext_1360_);
    v___x_1364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelAttr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_mkLabelAttr___closed__0_once),
        _init_l_Lean_mkLabelAttr___closed__0,
    );
    v___f_1365_ = leanh::lean_alloc_closure(
        l_Lean_mkLabelAttr___lam__2___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___f_1365_, 0, v_ext_1360_);
    leanh::lean_closure_set(v___f_1365_, 1, v___x_1364_);
    v___x_1366_ = 1;
    v___x_1367_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_1367_, 0, v_ref_1361_);
    leanh::lean_ctor_set(v___x_1367_, 1, v_attrName_1358_);
    leanh::lean_ctor_set(v___x_1367_, 2, v_attrDescr_1359_);
    leanh::lean_ctor_set_uint8(
        v___x_1367_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_1366_,
    );
    v___x_1368_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1368_, 0, v___x_1367_);
    leanh::lean_ctor_set(v___x_1368_, 1, v___f_1363_);
    leanh::lean_ctor_set(v___x_1368_, 2, v___f_1365_);
    v___x_1369_ = l_Lean_registerBuiltinAttribute(v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn l_Lean_mkLabelAttr___boxed(
    mut v_attrName_1370_: *mut leanh::LeanObject,
    mut v_attrDescr_1371_: *mut leanh::LeanObject,
    mut v_ext_1372_: *mut leanh::LeanObject,
    mut v_ref_1373_: *mut leanh::LeanObject,
    mut v_a_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Lean_mkLabelAttr(
        v_attrName_1370_,
        v_attrDescr_1371_,
        v_ext_1372_,
        v_ref_1373_,
    );
    return v_res_1375_;
}
pub unsafe fn _init_l_Lean_registerLabelAttr___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_mkLabelExt___auto__1___closed__28_once),
        _init_l_Lean_mkLabelExt___auto__1___closed__28,
    );
    return v___x_1376_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u64 = 0;
    v___x_1377_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1378_ = lean_uint64_of_nat(v___x_1377_);
    return v___x_1378_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_1379_: *mut leanh::LeanObject,
    mut v_x_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1389_: u64 = 0;
    let mut v___x_1390_: u64 = 0;
    let mut v___x_1391_: u64 = 0;
    let mut v_fold_1392_: u64 = 0;
    let mut v___x_1393_: u64 = 0;
    let mut v___x_1394_: u64 = 0;
    let mut v___x_1395_: u64 = 0;
    let mut v___x_1396_: usize = 0;
    let mut v___x_1397_: usize = 0;
    let mut v___x_1398_: usize = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: usize = 0;
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u64 = 0;
    let mut v_hash_1408_: u64 = 0;
    let mut v_isSharedCheck_1409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1380_) == 0 {
                    return v_x_1379_;
                } else {
                    v_key_1381_ = leanh::lean_ctor_get(v_x_1380_, 0);
                    v_value_1382_ = leanh::lean_ctor_get(v_x_1380_, 1);
                    v_tail_1383_ = leanh::lean_ctor_get(v_x_1380_, 2);
                    v_isSharedCheck_1409_ = (!leanh::lean_is_exclusive(v_x_1380_)) as u8;
                    if v_isSharedCheck_1409_ == 0 {
                        v___x_1385_ = v_x_1380_;
                        v_isShared_1386_ = v_isSharedCheck_1409_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1383_);
                        leanh::lean_inc(v_value_1382_);
                        leanh::lean_inc(v_key_1381_);
                        leanh::lean_dec(v_x_1380_);
                        v___x_1385_ = leanh::lean_box(0);
                        v_isShared_1386_ = v_isSharedCheck_1409_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1387_ = lean_array_get_size(v_x_1379_);
                if leanh::lean_obj_tag(v_key_1381_) == 0 {
                    v___x_1407_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1389_ = v___x_1407_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1408_ = leanh::lean_ctor_get_uint64(
                        v_key_1381_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1389_ = v_hash_1408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1390_ = 32u64;
                v___x_1391_ = lean_uint64_shift_right(v___y_1389_, v___x_1390_);
                v_fold_1392_ = lean_uint64_xor(v___y_1389_, v___x_1391_);
                v___x_1393_ = 16u64;
                v___x_1394_ = lean_uint64_shift_right(v_fold_1392_, v___x_1393_);
                v___x_1395_ = lean_uint64_xor(v_fold_1392_, v___x_1394_);
                v___x_1396_ = lean_uint64_to_usize(v___x_1395_);
                v___x_1397_ = lean_usize_of_nat(v___x_1387_);
                v___x_1398_ = 1usize;
                v___x_1399_ = lean_usize_sub(v___x_1397_, v___x_1398_);
                v___x_1400_ = lean_usize_land(v___x_1396_, v___x_1399_);
                v___x_1401_ = lean_array_uget_borrowed(v_x_1379_, v___x_1400_);
                leanh::lean_inc(v___x_1401_);
                if v_isShared_1386_ == 0 {
                    leanh::lean_ctor_set(v___x_1385_, 2, v___x_1401_);
                    v___x_1403_ = v___x_1385_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1406_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_key_1381_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_value_1382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1406_, 2, v___x_1401_);
                    v___x_1403_ = v_reuseFailAlloc_1406_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1404_ = lean_array_uset(v_x_1379_, v___x_1400_, v___x_1403_);
                v_x_1379_ = v___x_1404_;
                v_x_1380_ = v_tail_1383_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(
    mut v_i_1410_: *mut leanh::LeanObject,
    mut v_source_1411_: *mut leanh::LeanObject,
    mut v_target_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v_es_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1413_ = lean_array_get_size(v_source_1411_);
                v___x_1414_ = lean_nat_dec_lt(v_i_1410_, v___x_1413_);
                if v___x_1414_ == 0 {
                    leanh::lean_dec_ref(v_source_1411_);
                    leanh::lean_dec(v_i_1410_);
                    return v_target_1412_;
                } else {
                    v_es_1415_ = lean_array_fget(v_source_1411_, v_i_1410_);
                    v___x_1416_ = leanh::lean_box(0);
                    v_source_1417_ = lean_array_fset(v_source_1411_, v_i_1410_, v___x_1416_);
                    v_target_1418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_1412_, v_es_1415_);
                    v___x_1419_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1420_ = lean_nat_add(v_i_1410_, v___x_1419_);
                    leanh::lean_dec(v_i_1410_);
                    v_i_1410_ = v___x_1420_;
                    v_source_1411_ = v_source_1417_;
                    v_target_1412_ = v_target_1418_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(
    mut v_data_1422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = lean_array_get_size(v_data_1422_);
    v___x_1424_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1425_ = lean_nat_mul(v___x_1423_, v___x_1424_);
    v___x_1426_ = leanh::lean_unsigned_to_nat(0);
    v___x_1427_ = leanh::lean_box(0);
    v___x_1428_ = lean_mk_array(v_nbuckets_1425_, v___x_1427_);
    v___x_1429_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v___x_1426_, v_data_1422_, v___x_1428_);
    return v___x_1429_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(
    mut v_a_1430_: *mut leanh::LeanObject,
    mut v_x_1431_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1432_: u8 = 0;
    let mut v_key_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1431_) == 0 {
                    v___x_1432_ = 0;
                    return v___x_1432_;
                } else {
                    v_key_1433_ = leanh::lean_ctor_get(v_x_1431_, 0);
                    v_tail_1434_ = leanh::lean_ctor_get(v_x_1431_, 2);
                    v___x_1435_ = lean_name_eq(v_key_1433_, v_a_1430_);
                    if v___x_1435_ == 0 {
                        v_x_1431_ = v_tail_1434_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1435_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg___boxed(
    mut v_a_1437_: *mut leanh::LeanObject,
    mut v_x_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1439_: u8 = 0;
    let mut v_r_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_1437_, v_x_1438_);
    leanh::lean_dec(v_x_1438_);
    leanh::lean_dec(v_a_1437_);
    v_r_1440_ = leanh::lean_box((v_res_1439_) as usize);
    return v_r_1440_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(
    mut v_a_1441_: *mut leanh::LeanObject,
    mut v_b_1442_: *mut leanh::LeanObject,
    mut v_x_1443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1443_) == 0 {
                    leanh::lean_dec(v_b_1442_);
                    leanh::lean_dec(v_a_1441_);
                    return v_x_1443_;
                } else {
                    v_key_1444_ = leanh::lean_ctor_get(v_x_1443_, 0);
                    v_value_1445_ = leanh::lean_ctor_get(v_x_1443_, 1);
                    v_tail_1446_ = leanh::lean_ctor_get(v_x_1443_, 2);
                    v_isSharedCheck_1458_ = (!leanh::lean_is_exclusive(v_x_1443_)) as u8;
                    if v_isSharedCheck_1458_ == 0 {
                        v___x_1448_ = v_x_1443_;
                        v_isShared_1449_ = v_isSharedCheck_1458_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1446_);
                        leanh::lean_inc(v_value_1445_);
                        leanh::lean_inc(v_key_1444_);
                        leanh::lean_dec(v_x_1443_);
                        v___x_1448_ = leanh::lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1458_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1450_ = lean_name_eq(v_key_1444_, v_a_1441_);
                if v___x_1450_ == 0 {
                    v___x_1451_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_1441_, v_b_1442_, v_tail_1446_);
                    if v_isShared_1449_ == 0 {
                        leanh::lean_ctor_set(v___x_1448_, 2, v___x_1451_);
                        v___x_1453_ = v___x_1448_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1454_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_key_1444_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_value_1445_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 2, v___x_1451_);
                        v___x_1453_ = v_reuseFailAlloc_1454_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1445_);
                    leanh::lean_dec(v_key_1444_);
                    if v_isShared_1449_ == 0 {
                        leanh::lean_ctor_set(v___x_1448_, 1, v_b_1442_);
                        leanh::lean_ctor_set(v___x_1448_, 0, v_a_1441_);
                        v___x_1456_ = v___x_1448_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1457_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1441_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_b_1442_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_tail_1446_);
                        v___x_1456_ = v_reuseFailAlloc_1457_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1453_;
            }
            3 => {
                return v___x_1456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(
    mut v_m_1459_: *mut leanh::LeanObject,
    mut v_a_1460_: *mut leanh::LeanObject,
    mut v_b_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1469_: u64 = 0;
    let mut v___x_1470_: u64 = 0;
    let mut v___x_1471_: u64 = 0;
    let mut v_fold_1472_: u64 = 0;
    let mut v___x_1473_: u64 = 0;
    let mut v___x_1474_: u64 = 0;
    let mut v___x_1475_: u64 = 0;
    let mut v___x_1476_: usize = 0;
    let mut v___x_1477_: usize = 0;
    let mut v___x_1478_: usize = 0;
    let mut v___x_1479_: usize = 0;
    let mut v___x_1480_: usize = 0;
    let mut v_bkt_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v_val_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u64 = 0;
    let mut v_hash_1508_: u64 = 0;
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1462_ = leanh::lean_ctor_get(v_m_1459_, 0);
                v_buckets_1463_ = leanh::lean_ctor_get(v_m_1459_, 1);
                v_isSharedCheck_1509_ = (!leanh::lean_is_exclusive(v_m_1459_)) as u8;
                if v_isSharedCheck_1509_ == 0 {
                    v___x_1465_ = v_m_1459_;
                    v_isShared_1466_ = v_isSharedCheck_1509_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1463_);
                    leanh::lean_inc(v_size_1462_);
                    leanh::lean_dec(v_m_1459_);
                    v___x_1465_ = leanh::lean_box(0);
                    v_isShared_1466_ = v_isSharedCheck_1509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1467_ = lean_array_get_size(v_buckets_1463_);
                if leanh::lean_obj_tag(v_a_1460_) == 0 {
                    v___x_1507_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1469_ = v___x_1507_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1508_ = leanh::lean_ctor_get_uint64(
                        v_a_1460_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1469_ = v_hash_1508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1470_ = 32u64;
                v___x_1471_ = lean_uint64_shift_right(v___y_1469_, v___x_1470_);
                v_fold_1472_ = lean_uint64_xor(v___y_1469_, v___x_1471_);
                v___x_1473_ = 16u64;
                v___x_1474_ = lean_uint64_shift_right(v_fold_1472_, v___x_1473_);
                v___x_1475_ = lean_uint64_xor(v_fold_1472_, v___x_1474_);
                v___x_1476_ = lean_uint64_to_usize(v___x_1475_);
                v___x_1477_ = lean_usize_of_nat(v___x_1467_);
                v___x_1478_ = 1usize;
                v___x_1479_ = lean_usize_sub(v___x_1477_, v___x_1478_);
                v___x_1480_ = lean_usize_land(v___x_1476_, v___x_1479_);
                v_bkt_1481_ = lean_array_uget_borrowed(v_buckets_1463_, v___x_1480_);
                v___x_1482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_1460_, v_bkt_1481_);
                if v___x_1482_ == 0 {
                    v___x_1483_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1484_ = lean_nat_add(v_size_1462_, v___x_1483_);
                    leanh::lean_dec(v_size_1462_);
                    leanh::lean_inc(v_bkt_1481_);
                    v___x_1485_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1485_, 0, v_a_1460_);
                    leanh::lean_ctor_set(v___x_1485_, 1, v_b_1461_);
                    leanh::lean_ctor_set(v___x_1485_, 2, v_bkt_1481_);
                    v_buckets_x27_1486_ =
                        lean_array_uset(v_buckets_1463_, v___x_1480_, v___x_1485_);
                    v___x_1487_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1488_ = lean_nat_mul(v_size_x27_1484_, v___x_1487_);
                    v___x_1489_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1490_ = lean_nat_div(v___x_1488_, v___x_1489_);
                    leanh::lean_dec(v___x_1488_);
                    v___x_1491_ = lean_array_get_size(v_buckets_x27_1486_);
                    v___x_1492_ = lean_nat_dec_le(v___x_1490_, v___x_1491_);
                    leanh::lean_dec(v___x_1490_);
                    if v___x_1492_ == 0 {
                        v_val_1493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_buckets_x27_1486_);
                        if v_isShared_1466_ == 0 {
                            leanh::lean_ctor_set(v___x_1465_, 1, v_val_1493_);
                            leanh::lean_ctor_set(v___x_1465_, 0, v_size_x27_1484_);
                            v___x_1495_ = v___x_1465_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1496_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1496_,
                                0,
                                v_size_x27_1484_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_val_1493_);
                            v___x_1495_ = v_reuseFailAlloc_1496_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_1466_ == 0 {
                            leanh::lean_ctor_set(v___x_1465_, 1, v_buckets_x27_1486_);
                            leanh::lean_ctor_set(v___x_1465_, 0, v_size_x27_1484_);
                            v___x_1498_ = v___x_1465_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1499_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1499_,
                                0,
                                v_size_x27_1484_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1499_,
                                1,
                                v_buckets_x27_1486_,
                            );
                            v___x_1498_ = v_reuseFailAlloc_1499_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1481_);
                    v___x_1500_ = leanh::lean_box(0);
                    v_buckets_x27_1501_ =
                        lean_array_uset(v_buckets_1463_, v___x_1480_, v___x_1500_);
                    v___x_1502_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_1460_, v_b_1461_, v_bkt_1481_);
                    v___x_1503_ = lean_array_uset(v_buckets_x27_1501_, v___x_1480_, v___x_1502_);
                    if v_isShared_1466_ == 0 {
                        leanh::lean_ctor_set(v___x_1465_, 1, v___x_1503_);
                        v___x_1505_ = v___x_1465_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1506_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_size_1462_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1503_);
                        v___x_1505_ = v_reuseFailAlloc_1506_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1495_;
            }
            4 => {
                return v___x_1498_;
            }
            5 => {
                return v___x_1505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerLabelAttr(
    mut v_attrName_1510_: *mut leanh::LeanObject,
    mut v_attrDescr_1511_: *mut leanh::LeanObject,
    mut v_ref_1512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut v_unused_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1532_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_ref_1512_);
                v___x_1514_ = l_Lean_mkLabelExt(v_ref_1512_);
                if leanh::lean_obj_tag(v___x_1514_) == 0 {
                    v_a_1515_ = leanh::lean_ctor_get(v___x_1514_, 0);
                    leanh::lean_inc_n(v_a_1515_, 2);
                    leanh::lean_dec_ref_known(v___x_1514_, 1);
                    leanh::lean_inc(v_attrName_1510_);
                    v___x_1516_ = l_Lean_mkLabelAttr(
                        v_attrName_1510_,
                        v_attrDescr_1511_,
                        v_a_1515_,
                        v_ref_1512_,
                    );
                    if leanh::lean_obj_tag(v___x_1516_) == 0 {
                        v_isSharedCheck_1527_ =
                            (!leanh::lean_is_exclusive(v___x_1516_)) as u8;
                        if v_isSharedCheck_1527_ == 0 {
                            v_unused_1528_ = leanh::lean_ctor_get(v___x_1516_, 0);
                            leanh::lean_dec(v_unused_1528_);
                            v___x_1518_ = v___x_1516_;
                            v_isShared_1519_ = v_isSharedCheck_1527_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1516_);
                            v___x_1518_ = leanh::lean_box(0);
                            v_isShared_1519_ = v_isSharedCheck_1527_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1515_);
                        leanh::lean_dec(v_attrName_1510_);
                        v_a_1529_ = leanh::lean_ctor_get(v___x_1516_, 0);
                        v_isSharedCheck_1536_ =
                            (!leanh::lean_is_exclusive(v___x_1516_)) as u8;
                        if v_isSharedCheck_1536_ == 0 {
                            v___x_1531_ = v___x_1516_;
                            v_isShared_1532_ = v_isSharedCheck_1536_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1529_);
                            leanh::lean_dec(v___x_1516_);
                            v___x_1531_ = leanh::lean_box(0);
                            v_isShared_1532_ = v_isSharedCheck_1536_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_ref_1512_);
                    leanh::lean_dec_ref(v_attrDescr_1511_);
                    leanh::lean_dec(v_attrName_1510_);
                    return v___x_1514_;
                }
            }
            1 => {
                v___x_1520_ = l_Lean_labelExtensionMapRef;
                v___x_1521_ = lean_st_ref_take(v___x_1520_);
                leanh::lean_inc(v_a_1515_);
                v___x_1522_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(v___x_1521_, v_attrName_1510_, v_a_1515_);
                v___x_1523_ = lean_st_ref_set(v___x_1520_, v___x_1522_);
                if v_isShared_1519_ == 0 {
                    leanh::lean_ctor_set(v___x_1518_, 0, v_a_1515_);
                    v___x_1525_ = v___x_1518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1515_);
                    v___x_1525_ = v_reuseFailAlloc_1526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1525_;
            }
            3 => {
                if v_isShared_1532_ == 0 {
                    v___x_1534_ = v___x_1531_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
                    v___x_1534_ = v_reuseFailAlloc_1535_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_registerLabelAttr___boxed(
    mut v_attrName_1537_: *mut leanh::LeanObject,
    mut v_attrDescr_1538_: *mut leanh::LeanObject,
    mut v_ref_1539_: *mut leanh::LeanObject,
    mut v_a_1540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Lean_registerLabelAttr(v_attrName_1537_, v_attrDescr_1538_, v_ref_1539_);
    return v_res_1541_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0(
    mut v_00_u03b2_1542_: *mut leanh::LeanObject,
    mut v_m_1543_: *mut leanh::LeanObject,
    mut v_a_1544_: *mut leanh::LeanObject,
    mut v_b_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ =
        l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0___redArg(
            v_m_1543_, v_a_1544_, v_b_1545_,
        );
    return v___x_1546_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(
    mut v_00_u03b2_1547_: *mut leanh::LeanObject,
    mut v_a_1548_: *mut leanh::LeanObject,
    mut v_x_1549_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1550_: u8 = 0;
    v___x_1550_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___redArg(v_a_1548_, v_x_1549_);
    return v___x_1550_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0___boxed(
    mut v_00_u03b2_1551_: *mut leanh::LeanObject,
    mut v_a_1552_: *mut leanh::LeanObject,
    mut v_x_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1554_: u8 = 0;
    let mut v_r_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__0(v_00_u03b2_1551_, v_a_1552_, v_x_1553_);
    leanh::lean_dec(v_x_1553_);
    leanh::lean_dec(v_a_1552_);
    v_r_1555_ = leanh::lean_box((v_res_1554_) as usize);
    return v_r_1555_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1(
    mut v_00_u03b2_1556_: *mut leanh::LeanObject,
    mut v_data_1557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1___redArg(v_data_1557_);
    return v___x_1558_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2(
    mut v_00_u03b2_1559_: *mut leanh::LeanObject,
    mut v_a_1560_: *mut leanh::LeanObject,
    mut v_b_1561_: *mut leanh::LeanObject,
    mut v_x_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1563_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__2___redArg(v_a_1560_, v_b_1561_, v_x_1562_);
    return v___x_1563_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1564_: *mut leanh::LeanObject,
    mut v_i_1565_: *mut leanh::LeanObject,
    mut v_source_1566_: *mut leanh::LeanObject,
    mut v_target_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2___redArg(v_i_1565_, v_source_1566_, v_target_1567_);
    return v___x_1568_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1569_: *mut leanh::LeanObject,
    mut v_x_1570_: *mut leanh::LeanObject,
    mut v_x_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1572_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1570_, v_x_1571_);
    return v___x_1572_;
}
pub unsafe fn _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__12;
    v___x_1643_ = l_String_toRawSubstring_x27(v___x_1642_);
    return v___x_1643_;
}
pub unsafe fn _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__17;
    v___x_1654_ = l_String_toRawSubstring_x27(v___x_1653_);
    return v___x_1654_;
}
pub unsafe fn _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1665_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__23;
    v___x_1666_ = l_String_toRawSubstring_x27(v___x_1665_);
    return v___x_1666_;
}
pub unsafe fn _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1702_ = l_Lean_Parser_Command_registerLabelAttr___closed__2;
    v___x_1703_ = l_String_toRawSubstring_x27(v___x_1702_);
    return v___x_1703_;
}
pub unsafe fn _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51()
-> *mut leanh::LeanObject {
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1735_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1735_;
}
pub unsafe fn l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(
    mut v_x_1741_: *mut leanh::LeanObject,
    mut v_a_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1887_: u8 = 0;
    let mut v___y_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: u8 = 0;
    let mut v_idParser_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1926_: u8 = 0;
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1744_ = l_Lean_mkLabelExt___auto__1___closed__0;
                v___x_1745_ = l_Lean_mkLabelExt___auto__1___closed__1;
                v___x_1879_ = l_Lean_Parser_Command_registerLabelAttr___closed__3;
                leanh::lean_inc(v_x_1741_);
                v___x_1880_ = l_Lean_Syntax_isOfKind(v_x_1741_, v___x_1879_);
                if v___x_1880_ == 0 {
                    leanh::lean_dec(v_x_1741_);
                    v___x_1881_ = leanh::lean_box(1);
                    v___x_1882_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
                    leanh::lean_ctor_set(v___x_1882_, 1, v_a_1743_);
                    return v___x_1882_;
                } else {
                    v___x_1883_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1906_ = l_Lean_Syntax_getArg(v_x_1741_, v___x_1883_);
                    v___x_1907_ = leanh::lean_unsigned_to_nat(2);
                    v_id_1908_ = l_Lean_Syntax_getArg(v_x_1741_, v___x_1907_);
                    leanh::lean_dec(v_x_1741_);
                    v___x_1921_ = l_Lean_Syntax_getOptional_x3f(v___x_1906_);
                    leanh::lean_dec(v___x_1906_);
                    if leanh::lean_obj_tag(v___x_1921_) == 0 {
                        v___x_1922_ = leanh::lean_box(0);
                        v___y_1910_ = v___x_1922_;
                        state = 4;
                        continue;
                    } else {
                        v_val_1923_ = leanh::lean_ctor_get(v___x_1921_, 0);
                        v_isSharedCheck_1930_ =
                            (!leanh::lean_is_exclusive(v___x_1921_)) as u8;
                        if v_isSharedCheck_1930_ == 0 {
                            v___x_1925_ = v___x_1921_;
                            v_isShared_1926_ = v_isSharedCheck_1930_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1923_);
                            leanh::lean_dec(v___x_1921_);
                            v___x_1925_ = leanh::lean_box(0);
                            v_isShared_1926_ = v_isSharedCheck_1930_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_1769_);
                leanh::lean_inc_n(v___y_1751_, 5);
                leanh::lean_inc_n(v___y_1755_, 19);
                v___x_1770_ = l_Lean_Syntax_node3(
                    v___y_1755_,
                    v___y_1751_,
                    v___y_1769_,
                    v___y_1758_,
                    v___y_1769_,
                );
                leanh::lean_inc(v___y_1766_);
                v___x_1771_ =
                    l_Lean_Syntax_node2(v___y_1755_, v___y_1766_, v___y_1754_, v___x_1770_);
                leanh::lean_inc(v___y_1759_);
                v___x_1772_ = l_Lean_Syntax_node1(v___y_1755_, v___y_1759_, v___x_1771_);
                leanh::lean_inc_n(v___y_1767_, 4);
                leanh::lean_inc(v___y_1760_);
                v___x_1773_ =
                    l_Lean_Syntax_node2(v___y_1755_, v___y_1760_, v___x_1772_, v___y_1767_);
                v___x_1774_ = l_Lean_Syntax_node1(v___y_1755_, v___y_1751_, v___x_1773_);
                leanh::lean_inc(v___y_1747_);
                v___x_1775_ = l_Lean_Syntax_node1(v___y_1755_, v___y_1747_, v___x_1774_);
                leanh::lean_inc(v___y_1768_);
                v___x_1776_ = l_Lean_Syntax_node4(
                    v___y_1755_,
                    v___y_1768_,
                    v___y_1753_,
                    v___y_1764_,
                    v___y_1761_,
                    v___x_1775_,
                );
                v___x_1777_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__0;
                v___x_1778_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__1;
                v___x_1779_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__2;
                leanh::lean_inc_ref(v___y_1749_);
                v___x_1780_ =
                    l_Lean_Name_mkStr4(v___x_1744_, v___x_1745_, v___y_1749_, v___x_1779_);
                v___x_1781_ = l_Lean_Syntax_node1(v___y_1755_, v___x_1780_, v___y_1767_);
                v___x_1782_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1782_, 0, v___y_1755_);
                leanh::lean_ctor_set(v___x_1782_, 1, v___x_1777_);
                v___x_1783_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__4;
                v___x_1784_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__5;
                v___x_1785_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1785_, 0, v___y_1755_);
                leanh::lean_ctor_set(v___x_1785_, 1, v___x_1784_);
                v___x_1786_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__6;
                v___x_1787_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1787_, 0, v___y_1755_);
                leanh::lean_ctor_set(v___x_1787_, 1, v___x_1786_);
                v___x_1788_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__7;
                v___x_1789_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1789_, 0, v___y_1755_);
                leanh::lean_ctor_set(v___x_1789_, 1, v___x_1788_);
                v___x_1790_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__8;
                v___x_1791_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1791_, 0, v___y_1755_);
                leanh::lean_ctor_set(v___x_1791_, 1, v___x_1790_);
                v___x_1792_ = l_Lean_Syntax_node5(
                    v___y_1755_,
                    v___x_1783_,
                    v___x_1785_,
                    v___x_1787_,
                    v___x_1789_,
                    v___y_1750_,
                    v___x_1791_,
                );
                v___x_1793_ = l_Lean_Syntax_node1(v___y_1755_, v___y_1751_, v___x_1792_);
                v___x_1794_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__11;
                v___x_1795_ = l_Lean_Syntax_mkStrLit(v___y_1756_, v___y_1765_);
                v___x_1796_ = l_Lean_Syntax_node1(v___y_1755_, v___x_1794_, v___x_1795_);
                v___x_1797_ = l_Lean_Syntax_node1(v___y_1755_, v___y_1751_, v___x_1796_);
                v___x_1798_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13), core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13_once), _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__13);
                v___x_1799_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__14;
                leanh::lean_inc(v___y_1763_);
                leanh::lean_inc(v___y_1757_);
                v___x_1800_ = l_Lean_addMacroScope(v___y_1757_, v___x_1799_, v___y_1763_);
                v___x_1801_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1801_, 0, v___y_1755_);
                leanh::lean_ctor_set(v___x_1801_, 1, v___x_1798_);
                leanh::lean_ctor_set(v___x_1801_, 2, v___x_1800_);
                leanh::lean_ctor_set(v___x_1801_, 3, v___y_1748_);
                v___x_1802_ = leanh::lean_unsigned_to_nat(10);
                v___x_1803_ = lean_mk_empty_array_with_capacity(v___x_1802_);
                v___x_1804_ = lean_array_push(v___x_1803_, v___y_1752_);
                v___x_1805_ = lean_array_push(v___x_1804_, v___y_1767_);
                v___x_1806_ = lean_array_push(v___x_1805_, v___x_1781_);
                v___x_1807_ = lean_array_push(v___x_1806_, v___x_1782_);
                v___x_1808_ = lean_array_push(v___x_1807_, v___y_1767_);
                v___x_1809_ = lean_array_push(v___x_1808_, v___x_1793_);
                v___x_1810_ = lean_array_push(v___x_1809_, v___y_1767_);
                v___x_1811_ = lean_array_push(v___x_1810_, v___x_1797_);
                v___x_1812_ = lean_array_push(v___x_1811_, v___y_1762_);
                v___x_1813_ = lean_array_push(v___x_1812_, v___x_1801_);
                v___x_1814_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1814_, 0, v___y_1755_);
                leanh::lean_ctor_set(v___x_1814_, 1, v___x_1778_);
                leanh::lean_ctor_set(v___x_1814_, 2, v___x_1813_);
                v___x_1815_ =
                    l_Lean_Syntax_node2(v___y_1755_, v___y_1751_, v___x_1776_, v___x_1814_);
                v___x_1816_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1816_, 0, v___x_1815_);
                leanh::lean_ctor_set(v___x_1816_, 1, v_a_1743_);
                return v___x_1816_;
            }
            2 => {
                leanh::lean_inc_ref_n(v___y_1828_, 2);
                v___x_1832_ = l_Array_append___redArg(v___y_1828_, v___y_1831_);
                leanh::lean_dec_ref(v___y_1831_);
                leanh::lean_inc_n(v___y_1819_, 3);
                leanh::lean_inc_n(v___y_1823_, 12);
                v___x_1833_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1833_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1833_, 1, v___y_1819_);
                leanh::lean_ctor_set(v___x_1833_, 2, v___x_1832_);
                v___x_1834_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1834_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1834_, 1, v___y_1819_);
                leanh::lean_ctor_set(v___x_1834_, 2, v___y_1828_);
                leanh::lean_inc_ref_n(v___x_1834_, 6);
                leanh::lean_inc_ref(v___x_1833_);
                leanh::lean_inc(v___y_1821_);
                v___x_1835_ = l_Lean_Syntax_node7(
                    v___y_1823_,
                    v___y_1821_,
                    v___x_1833_,
                    v___x_1834_,
                    v___x_1834_,
                    v___x_1834_,
                    v___x_1834_,
                    v___x_1834_,
                    v___x_1834_,
                );
                v___x_1836_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__16;
                leanh::lean_inc_ref(v___y_1822_);
                v___x_1837_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1837_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1837_, 1, v___y_1822_);
                v___x_1838_ = l_Lean_Syntax_node1(v___y_1823_, v___x_1836_, v___x_1837_);
                v___x_1839_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18), core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18_once), _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__18);
                v___x_1840_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__19;
                leanh::lean_inc_n(v___y_1827_, 3);
                leanh::lean_inc_n(v___y_1825_, 3);
                v___x_1841_ = l_Lean_addMacroScope(v___y_1825_, v___x_1840_, v___y_1827_);
                v___x_1842_ = leanh::lean_box(0);
                v___x_1843_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1843_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1843_, 1, v___x_1839_);
                leanh::lean_ctor_set(v___x_1843_, 2, v___x_1841_);
                leanh::lean_ctor_set(v___x_1843_, 3, v___x_1842_);
                v___x_1844_ = l_Lean_mkLabelExt___auto__1___closed__14;
                v___x_1845_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__21;
                v___x_1846_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__22;
                v___x_1847_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1847_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1847_, 1, v___x_1846_);
                v___x_1848_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24), core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24_once), _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__24);
                v___x_1849_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__26;
                v___x_1850_ = l_Lean_addMacroScope(v___y_1825_, v___x_1849_, v___y_1827_);
                v___x_1851_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__28;
                v___x_1852_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1852_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1852_, 1, v___x_1848_);
                leanh::lean_ctor_set(v___x_1852_, 2, v___x_1850_);
                leanh::lean_ctor_set(v___x_1852_, 3, v___x_1851_);
                leanh::lean_inc_ref(v___x_1847_);
                v___x_1853_ =
                    l_Lean_Syntax_node2(v___y_1823_, v___x_1845_, v___x_1847_, v___x_1852_);
                v___x_1854_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__29;
                v___x_1855_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1855_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1855_, 1, v___x_1854_);
                v___x_1856_ = l_Lean_Syntax_node3(
                    v___y_1823_,
                    v___y_1819_,
                    v___x_1843_,
                    v___x_1853_,
                    v___x_1855_,
                );
                v___x_1857_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__31;
                v___x_1858_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__33;
                v___x_1859_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__35;
                v___x_1860_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__37;
                v___x_1861_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38), core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38_once), _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__38);
                v___x_1862_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__39;
                v___x_1863_ = l_Lean_addMacroScope(v___y_1825_, v___x_1862_, v___y_1827_);
                v___x_1864_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__42;
                v___x_1865_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1865_, 0, v___y_1823_);
                leanh::lean_ctor_set(v___x_1865_, 1, v___x_1861_);
                leanh::lean_ctor_set(v___x_1865_, 2, v___x_1863_);
                leanh::lean_ctor_set(v___x_1865_, 3, v___x_1864_);
                leanh::lean_inc(v___y_1818_);
                v___x_1866_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_1842_,
                    v___y_1818_,
                );
                if leanh::lean_obj_tag(v___x_1866_) == 0 {
                    v___x_1867_ = l_Lean_quoteNameMk(v___y_1818_);
                    v___y_1747_ = v___x_1857_;
                    v___y_1748_ = v___x_1842_;
                    v___y_1749_ = v___x_1844_;
                    v___y_1750_ = v___y_1820_;
                    v___y_1751_ = v___y_1819_;
                    v___y_1752_ = v___x_1833_;
                    v___y_1753_ = v___x_1835_;
                    v___y_1754_ = v___x_1865_;
                    v___y_1755_ = v___y_1823_;
                    v___y_1756_ = v___y_1824_;
                    v___y_1757_ = v___y_1825_;
                    v___y_1758_ = v___y_1826_;
                    v___y_1759_ = v___x_1859_;
                    v___y_1760_ = v___x_1858_;
                    v___y_1761_ = v___x_1856_;
                    v___y_1762_ = v___x_1847_;
                    v___y_1763_ = v___y_1827_;
                    v___y_1764_ = v___x_1838_;
                    v___y_1765_ = v___y_1829_;
                    v___y_1766_ = v___x_1860_;
                    v___y_1767_ = v___x_1834_;
                    v___y_1768_ = v___y_1830_;
                    v___y_1769_ = v___x_1867_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1818_);
                    v_val_1868_ = leanh::lean_ctor_get(v___x_1866_, 0);
                    leanh::lean_inc(v_val_1868_);
                    leanh::lean_dec_ref_known(v___x_1866_, 1);
                    v___x_1869_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__44;
                    v___x_1870_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__45;
                    v___x_1871_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__46;
                    v___x_1872_ = lean_string_intercalate(v___x_1871_, v_val_1868_);
                    v___x_1873_ = lean_string_append(v___x_1870_, v___x_1872_);
                    leanh::lean_dec_ref(v___x_1872_);
                    leanh::lean_inc_n(v___y_1829_, 2);
                    v___x_1874_ = l_Lean_Syntax_mkNameLit(v___x_1873_, v___y_1829_);
                    v___x_1875_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1876_ = lean_mk_empty_array_with_capacity(v___x_1875_);
                    v___x_1877_ = lean_array_push(v___x_1876_, v___x_1874_);
                    v___x_1878_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1878_, 0, v___y_1829_);
                    leanh::lean_ctor_set(v___x_1878_, 1, v___x_1869_);
                    leanh::lean_ctor_set(v___x_1878_, 2, v___x_1877_);
                    v___y_1747_ = v___x_1857_;
                    v___y_1748_ = v___x_1842_;
                    v___y_1749_ = v___x_1844_;
                    v___y_1750_ = v___y_1820_;
                    v___y_1751_ = v___y_1819_;
                    v___y_1752_ = v___x_1833_;
                    v___y_1753_ = v___x_1835_;
                    v___y_1754_ = v___x_1865_;
                    v___y_1755_ = v___y_1823_;
                    v___y_1756_ = v___y_1824_;
                    v___y_1757_ = v___y_1825_;
                    v___y_1758_ = v___y_1826_;
                    v___y_1759_ = v___x_1859_;
                    v___y_1760_ = v___x_1858_;
                    v___y_1761_ = v___x_1856_;
                    v___y_1762_ = v___x_1847_;
                    v___y_1763_ = v___y_1827_;
                    v___y_1764_ = v___x_1838_;
                    v___y_1765_ = v___y_1829_;
                    v___y_1766_ = v___x_1860_;
                    v___y_1767_ = v___x_1834_;
                    v___y_1768_ = v___y_1830_;
                    v___y_1769_ = v___x_1878_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_quotContext_1891_ = leanh::lean_ctor_get(v_a_1742_, 1);
                v_currMacroScope_1892_ = leanh::lean_ctor_get(v_a_1742_, 2);
                v_ref_1893_ = leanh::lean_ctor_get(v_a_1742_, 5);
                v___x_1894_ = l_String_removeLeadingSpaces(v___y_1890_);
                v___x_1895_ = leanh::lean_box(2);
                v___x_1896_ = l_Lean_Syntax_mkStrLit(v___x_1894_, v___x_1895_);
                v___x_1897_ = l_Lean_SourceInfo_fromRef(v_ref_1893_, v___y_1887_);
                v___x_1898_ = l_Lean_mkLabelExt___auto__1___closed__9;
                v___x_1899_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__47;
                v___x_1900_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__48;
                v___x_1901_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__50;
                v___x_1902_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51), core::ptr::addr_of_mut!(l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51_once), _init_l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__51);
                if leanh::lean_obj_tag(v___y_1889_) == 1 {
                    v_val_1903_ = leanh::lean_ctor_get(v___y_1889_, 0);
                    leanh::lean_inc(v_val_1903_);
                    leanh::lean_dec_ref_known(v___y_1889_, 1);
                    v___x_1904_ = l_Array_mkArray1___redArg(v_val_1903_);
                    v___y_1818_ = v___y_1886_;
                    v___y_1819_ = v___x_1898_;
                    v___y_1820_ = v___y_1888_;
                    v___y_1821_ = v___x_1901_;
                    v___y_1822_ = v___x_1899_;
                    v___y_1823_ = v___x_1897_;
                    v___y_1824_ = v___y_1885_;
                    v___y_1825_ = v_quotContext_1891_;
                    v___y_1826_ = v___x_1896_;
                    v___y_1827_ = v_currMacroScope_1892_;
                    v___y_1828_ = v___x_1902_;
                    v___y_1829_ = v___x_1895_;
                    v___y_1830_ = v___x_1900_;
                    v___y_1831_ = v___x_1904_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1889_);
                    v___x_1905_ = l_Lean_mkLabelExt___auto__1___closed__5;
                    v___y_1818_ = v___y_1886_;
                    v___y_1819_ = v___x_1898_;
                    v___y_1820_ = v___y_1888_;
                    v___y_1821_ = v___x_1901_;
                    v___y_1822_ = v___x_1899_;
                    v___y_1823_ = v___x_1897_;
                    v___y_1824_ = v___y_1885_;
                    v___y_1825_ = v_quotContext_1891_;
                    v___y_1826_ = v___x_1896_;
                    v___y_1827_ = v_currMacroScope_1892_;
                    v___y_1828_ = v___x_1902_;
                    v___y_1829_ = v___x_1895_;
                    v___y_1830_ = v___x_1900_;
                    v___y_1831_ = v___x_1905_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1911_ = l_Lean_TSyntax_getId(v_id_1908_);
                leanh::lean_inc_n(v___x_1911_, 2);
                v_str_1912_ = l_Lean_Name_toString(v___x_1911_, v___x_1880_);
                v___x_1913_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__53;
                v___x_1914_ = l_Lean_Name_append(v___x_1913_, v___x_1911_);
                v___x_1915_ = 0;
                v_idParser_1916_ = l_Lean_mkIdentFrom(v_id_1908_, v___x_1914_, v___x_1915_);
                leanh::lean_dec(v_id_1908_);
                if leanh::lean_obj_tag(v___y_1910_) == 0 {
                    v___x_1917_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___closed__54;
                    v___x_1918_ = lean_string_append(v___x_1917_, v_str_1912_);
                    v___y_1885_ = v_str_1912_;
                    v___y_1886_ = v___x_1911_;
                    v___y_1887_ = v___x_1915_;
                    v___y_1888_ = v_idParser_1916_;
                    v___y_1889_ = v___y_1910_;
                    v___y_1890_ = v___x_1918_;
                    state = 3;
                    continue;
                } else {
                    v_val_1919_ = leanh::lean_ctor_get(v___y_1910_, 0);
                    v___x_1920_ = l_Lean_TSyntax_getDocString(v_val_1919_);
                    v___y_1885_ = v_str_1912_;
                    v___y_1886_ = v___x_1911_;
                    v___y_1887_ = v___x_1915_;
                    v___y_1888_ = v_idParser_1916_;
                    v___y_1889_ = v___y_1910_;
                    v___y_1890_ = v___x_1920_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                if v_isShared_1926_ == 0 {
                    v___x_1928_ = v___x_1925_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_val_1923_);
                    v___x_1928_ = v_reuseFailAlloc_1929_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_1910_ = v___x_1928_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1___boxed(
    mut v_x_1931_: *mut leanh::LeanObject,
    mut v_a_1932_: *mut leanh::LeanObject,
    mut v_a_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Lean___aux__Lean__LabelAttribute______macroRules__Lean____root____Lean__Parser__Command__registerLabelAttr__1(v_x_1931_, v_a_1932_, v_a_1933_);
    leanh::lean_dec_ref(v_a_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_x_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1936_) == 0 {
                    v___x_1937_ = leanh::lean_box(0);
                    return v___x_1937_;
                } else {
                    v_key_1938_ = leanh::lean_ctor_get(v_x_1936_, 0);
                    v_value_1939_ = leanh::lean_ctor_get(v_x_1936_, 1);
                    v_tail_1940_ = leanh::lean_ctor_get(v_x_1936_, 2);
                    v___x_1941_ = lean_name_eq(v_key_1938_, v_a_1935_);
                    if v___x_1941_ == 0 {
                        v_x_1936_ = v_tail_1940_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1939_);
                        v___x_1943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1943_, 0, v_value_1939_);
                        return v___x_1943_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg___boxed(
    mut v_a_1944_: *mut leanh::LeanObject,
    mut v_x_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1946_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_1944_, v_x_1945_);
    leanh::lean_dec(v_x_1945_);
    leanh::lean_dec(v_a_1944_);
    return v_res_1946_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(
    mut v_m_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1952_: u64 = 0;
    let mut v___x_1953_: u64 = 0;
    let mut v___x_1954_: u64 = 0;
    let mut v_fold_1955_: u64 = 0;
    let mut v___x_1956_: u64 = 0;
    let mut v___x_1957_: u64 = 0;
    let mut v___x_1958_: u64 = 0;
    let mut v___x_1959_: usize = 0;
    let mut v___x_1960_: usize = 0;
    let mut v___x_1961_: usize = 0;
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u64 = 0;
    let mut v_hash_1967_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1949_ = leanh::lean_ctor_get(v_m_1947_, 1);
                v___x_1950_ = lean_array_get_size(v_buckets_1949_);
                if leanh::lean_obj_tag(v_a_1948_) == 0 {
                    v___x_1966_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerLabelAttr_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1952_ = v___x_1966_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1967_ = leanh::lean_ctor_get_uint64(
                        v_a_1948_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1952_ = v_hash_1967_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1953_ = 32u64;
                v___x_1954_ = lean_uint64_shift_right(v___y_1952_, v___x_1953_);
                v_fold_1955_ = lean_uint64_xor(v___y_1952_, v___x_1954_);
                v___x_1956_ = 16u64;
                v___x_1957_ = lean_uint64_shift_right(v_fold_1955_, v___x_1956_);
                v___x_1958_ = lean_uint64_xor(v_fold_1955_, v___x_1957_);
                v___x_1959_ = lean_uint64_to_usize(v___x_1958_);
                v___x_1960_ = lean_usize_of_nat(v___x_1950_);
                v___x_1961_ = 1usize;
                v___x_1962_ = lean_usize_sub(v___x_1960_, v___x_1961_);
                v___x_1963_ = lean_usize_land(v___x_1959_, v___x_1962_);
                v___x_1964_ = lean_array_uget_borrowed(v_buckets_1949_, v___x_1963_);
                v___x_1965_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_1948_, v___x_1964_);
                return v___x_1965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg___boxed(
    mut v_m_1968_: *mut leanh::LeanObject,
    mut v_a_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(
            v_m_1968_, v_a_1969_,
        );
    leanh::lean_dec(v_a_1969_);
    leanh::lean_dec_ref(v_m_1968_);
    return v_res_1970_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1971_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__0);
    v___x_1973_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1973_, 0, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
    v___x_1975_ = leanh::lean_unsigned_to_nat(0);
    v___x_1976_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1976_, 0, v___x_1975_);
    leanh::lean_ctor_set(v___x_1976_, 1, v___x_1975_);
    leanh::lean_ctor_set(v___x_1976_, 2, v___x_1975_);
    leanh::lean_ctor_set(v___x_1976_, 3, v___x_1975_);
    leanh::lean_ctor_set(v___x_1976_, 4, v___x_1974_);
    leanh::lean_ctor_set(v___x_1976_, 5, v___x_1974_);
    leanh::lean_ctor_set(v___x_1976_, 6, v___x_1974_);
    leanh::lean_ctor_set(v___x_1976_, 7, v___x_1974_);
    leanh::lean_ctor_set(v___x_1976_, 8, v___x_1974_);
    leanh::lean_ctor_set(v___x_1976_, 9, v___x_1974_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = leanh::lean_unsigned_to_nat(32);
    v___x_1978_ = lean_mk_empty_array_with_capacity(v___x_1977_);
    v___x_1979_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1979_, 0, v___x_1978_);
    return v___x_1979_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1980_: usize = 0;
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = 5usize;
    v___x_1981_ = leanh::lean_unsigned_to_nat(0);
    v___x_1982_ = leanh::lean_unsigned_to_nat(32);
    v___x_1983_ = lean_mk_empty_array_with_capacity(v___x_1982_);
    v___x_1984_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__3);
    v___x_1985_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1985_, 0, v___x_1984_);
    leanh::lean_ctor_set(v___x_1985_, 1, v___x_1983_);
    leanh::lean_ctor_set(v___x_1985_, 2, v___x_1981_);
    leanh::lean_ctor_set(v___x_1985_, 3, v___x_1981_);
    leanh::lean_ctor_set_usize(v___x_1985_, 4, v___x_1980_);
    return v___x_1985_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = leanh::lean_box(1);
    v___x_1987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__4);
    v___x_1988_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__1);
    v___x_1989_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1989_, 0, v___x_1988_);
    leanh::lean_ctor_set(v___x_1989_, 1, v___x_1987_);
    leanh::lean_ctor_set(v___x_1989_, 2, v___x_1986_);
    return v___x_1989_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(
    mut v_msgData_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = lean_st_ref_get(v___y_1992_);
    v_env_1995_ = leanh::lean_ctor_get(v___x_1994_, 0);
    leanh::lean_inc_ref(v_env_1995_);
    leanh::lean_dec(v___x_1994_);
    v_options_1996_ = leanh::lean_ctor_get(v___y_1991_, 2);
    v___x_1997_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__2);
    v___x_1998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___closed__5);
    leanh::lean_inc_ref(v_options_1996_);
    v___x_1999_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1999_, 0, v_env_1995_);
    leanh::lean_ctor_set(v___x_1999_, 1, v___x_1997_);
    leanh::lean_ctor_set(v___x_1999_, 2, v___x_1998_);
    leanh::lean_ctor_set(v___x_1999_, 3, v_options_1996_);
    v___x_2000_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2000_, 0, v___x_1999_);
    leanh::lean_ctor_set(v___x_2000_, 1, v_msgData_1990_);
    v___x_2001_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2001_, 0, v___x_2000_);
    return v___x_2001_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2___boxed(
    mut v_msgData_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2006_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msgData_2002_, v___y_2003_, v___y_2004_);
    leanh::lean_dec(v___y_2004_);
    leanh::lean_dec_ref(v___y_2003_);
    return v_res_2006_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(
    mut v_msg_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2011_ = leanh::lean_ctor_get(v___y_2008_, 5);
                v___x_2012_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_labelled_spec__1_spec__2(v_msg_2007_, v___y_2008_, v___y_2009_);
                v_a_2013_ = leanh::lean_ctor_get(v___x_2012_, 0);
                v_isSharedCheck_2021_ = (!leanh::lean_is_exclusive(v___x_2012_)) as u8;
                if v_isSharedCheck_2021_ == 0 {
                    v___x_2015_ = v___x_2012_;
                    v_isShared_2016_ = v_isSharedCheck_2021_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2013_);
                    leanh::lean_dec(v___x_2012_);
                    v___x_2015_ = leanh::lean_box(0);
                    v_isShared_2016_ = v_isSharedCheck_2021_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2011_);
                v___x_2017_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2017_, 0, v_ref_2011_);
                leanh::lean_ctor_set(v___x_2017_, 1, v_a_2013_);
                if v_isShared_2016_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2015_, 1);
                    leanh::lean_ctor_set(v___x_2015_, 0, v___x_2017_);
                    v___x_2019_ = v___x_2015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2020_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
                    v___x_2019_ = v_reuseFailAlloc_2020_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_labelled_spec__1___redArg___boxed(
    mut v_msg_2022_: *mut leanh::LeanObject,
    mut v___y_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(
        v_msg_2022_,
        v___y_2023_,
        v___y_2024_,
    );
    leanh::lean_dec(v___y_2024_);
    leanh::lean_dec_ref(v___y_2023_);
    return v_res_2026_;
}
pub unsafe fn _init_l_Lean_labelled___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Lean_labelled___closed__0;
    v___x_2029_ = l_Lean_stringToMessageData(v___x_2028_);
    return v___x_2029_;
}
pub unsafe fn l_Lean_labelled(
    mut v_attrName_2030_: *mut leanh::LeanObject,
    mut v_a_2031_: *mut leanh::LeanObject,
    mut v_a_2032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2034_ = l_Lean_labelExtensionMapRef;
                v___x_2035_ = lean_st_ref_get(v___x_2034_);
                v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(v___x_2035_, v_attrName_2030_);
                leanh::lean_dec(v___x_2035_);
                if leanh::lean_obj_tag(v___x_2036_) == 0 {
                    v___x_2037_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_labelled___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_labelled___closed__1_once),
                        _init_l_Lean_labelled___closed__1,
                    );
                    v___x_2038_ = l_Lean_MessageData_ofName(v_attrName_2030_);
                    v___x_2039_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2039_, 0, v___x_2037_);
                    leanh::lean_ctor_set(v___x_2039_, 1, v___x_2038_);
                    v___x_2040_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(
                        v___x_2039_,
                        v_a_2031_,
                        v_a_2032_,
                    );
                    return v___x_2040_;
                } else {
                    leanh::lean_dec(v_attrName_2030_);
                    v_val_2041_ = leanh::lean_ctor_get(v___x_2036_, 0);
                    v_isSharedCheck_2055_ = (!leanh::lean_is_exclusive(v___x_2036_)) as u8;
                    if v_isSharedCheck_2055_ == 0 {
                        v___x_2043_ = v___x_2036_;
                        v_isShared_2044_ = v_isSharedCheck_2055_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2041_);
                        leanh::lean_dec(v___x_2036_);
                        v___x_2043_ = leanh::lean_box(0);
                        v_isShared_2044_ = v_isSharedCheck_2055_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2045_ = lean_st_ref_get(v_a_2032_);
                v_ext_2046_ = leanh::lean_ctor_get(v_val_2041_, 1);
                v_toEnvExtension_2047_ = leanh::lean_ctor_get(v_ext_2046_, 0);
                v_env_2048_ = leanh::lean_ctor_get(v___x_2045_, 0);
                leanh::lean_inc_ref(v_env_2048_);
                leanh::lean_dec(v___x_2045_);
                v_asyncMode_2049_ = leanh::lean_ctor_get(v_toEnvExtension_2047_, 2);
                leanh::lean_inc(v_asyncMode_2049_);
                v___x_2050_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_mkLabelAttr___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_mkLabelAttr___closed__0_once),
                    _init_l_Lean_mkLabelAttr___closed__0,
                );
                v___x_2051_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_2050_,
                    v_val_2041_,
                    v_env_2048_,
                    v_asyncMode_2049_,
                );
                leanh::lean_dec(v_asyncMode_2049_);
                leanh::lean_dec(v_val_2041_);
                if v_isShared_2044_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2043_, 0);
                    leanh::lean_ctor_set(v___x_2043_, 0, v___x_2051_);
                    v___x_2053_ = v___x_2043_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_labelled___boxed(
    mut v_attrName_2056_: *mut leanh::LeanObject,
    mut v_a_2057_: *mut leanh::LeanObject,
    mut v_a_2058_: *mut leanh::LeanObject,
    mut v_a_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2060_ = l_Lean_labelled(v_attrName_2056_, v_a_2057_, v_a_2058_);
    leanh::lean_dec(v_a_2058_);
    leanh::lean_dec_ref(v_a_2057_);
    return v_res_2060_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(
    mut v_00_u03b2_2061_: *mut leanh::LeanObject,
    mut v_m_2062_: *mut leanh::LeanObject,
    mut v_a_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___redArg(
            v_m_2062_, v_a_2063_,
        );
    return v___x_2064_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0___boxed(
    mut v_00_u03b2_2065_: *mut leanh::LeanObject,
    mut v_m_2066_: *mut leanh::LeanObject,
    mut v_a_2067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0(
        v_00_u03b2_2065_,
        v_m_2066_,
        v_a_2067_,
    );
    leanh::lean_dec(v_a_2067_);
    leanh::lean_dec_ref(v_m_2066_);
    return v_res_2068_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_labelled_spec__1(
    mut v_00_u03b1_2069_: *mut leanh::LeanObject,
    mut v_msg_2070_: *mut leanh::LeanObject,
    mut v___y_2071_: *mut leanh::LeanObject,
    mut v___y_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_throwError___at___00Lean_labelled_spec__1___redArg(
        v_msg_2070_,
        v___y_2071_,
        v___y_2072_,
    );
    return v___x_2074_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_labelled_spec__1___boxed(
    mut v_00_u03b1_2075_: *mut leanh::LeanObject,
    mut v_msg_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lean_throwError___at___00Lean_labelled_spec__1(
        v_00_u03b1_2075_,
        v_msg_2076_,
        v___y_2077_,
        v___y_2078_,
    );
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    return v_res_2080_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(
    mut v_00_u03b2_2081_: *mut leanh::LeanObject,
    mut v_a_2082_: *mut leanh::LeanObject,
    mut v_x_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___redArg(v_a_2082_, v_x_2083_);
    return v___x_2084_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0___boxed(
    mut v_00_u03b2_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
    mut v_x_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2088_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_labelled_spec__0_spec__0(v_00_u03b2_2085_, v_a_2086_, v_x_2087_);
    leanh::lean_dec(v_x_2087_);
    leanh::lean_dec(v_a_2086_);
    return v_res_2088_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_LabelAttribute(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_DocString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_LabelAttribute_0__Lean_initFn_00___x40_Lean_LabelAttribute_897315755____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_labelExtensionMapRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_labelExtensionMapRef);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_LabelAttribute(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_String_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_mkLabelExt___auto__1 = _init_l_Lean_mkLabelExt___auto__1();
    leanh::lean_mark_persistent(l_Lean_mkLabelExt___auto__1);
    l_Lean_mkLabelAttr___auto__1 = _init_l_Lean_mkLabelAttr___auto__1();
    leanh::lean_mark_persistent(l_Lean_mkLabelAttr___auto__1);
    l_Lean_registerLabelAttr___auto__1 = _init_l_Lean_registerLabelAttr___auto__1();
    leanh::lean_mark_persistent(l_Lean_registerLabelAttr___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_LabelAttribute(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_DocString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LabelAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_LabelAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_LabelAttribute(builtin);
}