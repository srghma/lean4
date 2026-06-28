// Lean compiler output
// Module: Lean.Elab.Mixfix
// Imports: Lean.Elab.Attributes Init.Syntax
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit, l_Lean_evalPrec,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_throwUnsupported___redArg,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::{
    initialize_Init_Syntax, l_Lean_Syntax_setArg, runtime_initialize_Init_Syntax,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Attributes::{
    initialize_Lean_Elab_Attributes, l_Lean_Elab_mkAttrKindGlobal,
    runtime_initialize_Lean_Elab_Attributes,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value: LeanStringObject<10> =
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
        m_data: [105, 100, 101, 110, 116, 80, 114, 101, 99, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__3_value)
                as *mut LeanObject,
            9101404829963262459 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value: LeanStringObject<4> =
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
        m_data: [97, 114, 103, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__5_value)
                as *mut LeanObject,
            6287119281958077034 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value: LeanStringObject<3> =
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
        m_data: [61, 62, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value: LeanStringObject<4> =
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
        m_data: [97, 112, 112, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value: LeanStringObject<4> =
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
        m_data: [108, 104, 115, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__10_value)
                as *mut LeanObject,
            5328765574789290742 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value: LeanStringObject<4> =
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
        m_data: [114, 104, 115, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__13_value)
                as *mut LeanObject,
            969147236311963285 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value: LeanStringObject<7> =
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
        m_data: [109, 105, 120, 102, 105, 120, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__16_value)
                as *mut LeanObject,
            43679389351681793 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value: LeanStringObject<10> =
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
        m_data: [110, 97, 109, 101, 100, 80, 114, 105, 111, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__18_value)
                as *mut LeanObject,
            13348752267415789739 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value: LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value: LeanStringObject<9> =
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
        m_data: [112, 114, 105, 111, 114, 105, 116, 121, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value: LeanStringObject<3> =
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
        m_data: [58, 61, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value: LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__25_value: LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value: LeanStringObject<10> =
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
        m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__26_value)
                as *mut LeanObject,
            17682753938374962505 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value: LeanStringObject<11> =
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
        m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value: LeanStringObject<3> =
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
        m_data: [64, 91, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value: LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value: LeanStringObject<9> =
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
        m_data: [110, 111, 116, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__32_value)
                as *mut LeanObject,
            13116756686754095629 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__34_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__35_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__36: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value: LeanStringObject<9> =
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
        m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__38_value)
                as *mut LeanObject,
            7983999284776576032 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__39_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value: LeanStringObject<7> =
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
        m_data: [105, 110, 102, 105, 120, 108, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__40_value)
                as *mut LeanObject,
            12494365462036000886 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__41_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value: LeanStringObject<6> =
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
        m_data: [105, 110, 102, 105, 120, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__42_value)
                as *mut LeanObject,
            10188811159498705416 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__43_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value: LeanStringObject<7> =
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
        m_data: [105, 110, 102, 105, 120, 114, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__44_value)
                as *mut LeanObject,
            16268699076359030537 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__45_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value: LeanStringObject<7> =
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
        m_data: [112, 114, 101, 102, 105, 120, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__46_value)
                as *mut LeanObject,
            11805246081692270559 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__47_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 111, 115, 116, 102, 105, 120, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__48_value)
                as *mut LeanObject,
            760317308010147681 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__49_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value: LeanStringObject<11> =
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
        m_data: [112, 114, 101, 99, 101, 100, 101, 110, 99, 101, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__50_value)
                as *mut LeanObject,
            11586196343691998021 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__51_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__37_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__29_value)
                as *mut LeanObject,
            2533412339571800130 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__52_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value: LeanStringObject<11> =
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
        m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__53_value)
                as *mut LeanObject,
            9063780239635860524 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_expandMixfix___lam__0___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_expandMixfix___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Command_expandMixfix___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Command_expandMixfix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 112, 97, 110, 100, 77, 105, 120, 102, 105, 120, 0]};
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__2_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__1_value) as *mut LeanObject,15249639513547833186 as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__0_value) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__1_value) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 11 as usize) << 1) | 1) as *mut LeanObject,((( 60 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__3_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__4_value) as *mut LeanObject,((( 60 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(
    mut v_stx_1497_: *mut LeanObject,
    mut v_f_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrKind_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v_a_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1501_ = lean_unsigned_to_nat(2);
                v_attrKind_1502_ = l_Lean_Syntax_getArg(v_stx_1497_, v___x_1501_);
                v___x_1503_ = l_Lean_Elab_mkAttrKindGlobal;
                v_stx_1504_ = l_Lean_Syntax_setArg(v_stx_1497_, v___x_1501_, v___x_1503_);
                lean_inc_ref(v_a_1499_);
                v___x_1505_ = lean_apply_3(v_f_1498_, v_stx_1504_, v_a_1499_, v_a_1500_);
                if lean_obj_tag(v___x_1505_) == 0 {
                    v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
                    v_a_1507_ = lean_ctor_get(v___x_1505_, 1);
                    v_isSharedCheck_1515_ = (!lean_is_exclusive(v___x_1505_)) as u8;
                    if v_isSharedCheck_1515_ == 0 {
                        v___x_1509_ = v___x_1505_;
                        v_isShared_1510_ = v_isSharedCheck_1515_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1507_);
                        lean_inc(v_a_1506_);
                        lean_dec(v___x_1505_);
                        v___x_1509_ = lean_box(0);
                        v_isShared_1510_ = v_isSharedCheck_1515_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_attrKind_1502_);
                    v_a_1516_ = lean_ctor_get(v___x_1505_, 0);
                    v_a_1517_ = lean_ctor_get(v___x_1505_, 1);
                    v_isSharedCheck_1524_ = (!lean_is_exclusive(v___x_1505_)) as u8;
                    if v_isSharedCheck_1524_ == 0 {
                        v___x_1519_ = v___x_1505_;
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1517_);
                        lean_inc(v_a_1516_);
                        lean_dec(v___x_1505_);
                        v___x_1519_ = lean_box(0);
                        v_isShared_1520_ = v_isSharedCheck_1524_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1511_ = l_Lean_Syntax_setArg(v_a_1506_, v___x_1501_, v_attrKind_1502_);
                if v_isShared_1510_ == 0 {
                    lean_ctor_set(v___x_1509_, 0, v___x_1511_);
                    v___x_1513_ = v___x_1509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
                    lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_a_1507_);
                    v___x_1513_ = v_reuseFailAlloc_1514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1513_;
            }
            3 => {
                if v_isShared_1520_ == 0 {
                    v___x_1522_ = v___x_1519_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1516_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_a_1517_);
                    v___x_1522_ = v_reuseFailAlloc_1523_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal___boxed(
    mut v_stx_1525_: *mut LeanObject,
    mut v_f_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1529_: *mut LeanObject = core::ptr::null_mut();
    v_res_1529_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(
        v_stx_1525_,
        v_f_1526_,
        v_a_1527_,
        v_a_1528_,
    );
    lean_dec_ref(v_a_1527_);
    return v_res_1529_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6() -> *mut LeanObject {
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    v___x_1540_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__5;
    v___x_1541_ = l_String_toRawSubstring_x27(v___x_1540_);
    return v___x_1541_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11() -> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__10;
    v___x_1548_ = l_String_toRawSubstring_x27(v___x_1547_);
    return v___x_1548_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14() -> *mut LeanObject {
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1552_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__13;
    v___x_1553_ = l_String_toRawSubstring_x27(v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36() -> *mut LeanObject {
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Array_mkArray0(lean_box(0));
    return v___x_1594_;
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix___lam__0(
    mut v_stx_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: u8 = 0;
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2037_: u8 = 0;
    let mut v___y_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2064_: u8 = 0;
    let mut v___y_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: u8 = 0;
    let mut v___y_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: u8 = 0;
    let mut v___y_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2359_: u8 = 0;
    let mut v___y_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut v___y_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: u8 = 0;
    let mut v___y_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: u8 = 0;
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: u8 = 0;
    let mut v___y_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v___y_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2587_: u8 = 0;
    let mut v___y_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: u8 = 0;
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v___y_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: u8 = 0;
    let mut v___x_2778_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: u8 = 0;
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prio_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: u8 = 0;
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u8 = 0;
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: u8 = 0;
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: u8 = 0;
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: u8 = 0;
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1651_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__0;
                v___x_1652_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__1;
                v___x_1923_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__17;
                lean_inc(v_stx_1648_);
                v___x_1924_ = l_Lean_Syntax_isOfKind(v_stx_1648_, v___x_1923_);
                if v___x_1924_ == 0 {
                    lean_dec(v_stx_1648_);
                    v___x_1925_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1650_);
                    return v___x_1925_;
                } else {
                    v___x_1926_ = lean_unsigned_to_nat(0);
                    v___x_2922_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_1926_);
                    v___x_2923_ = l_Lean_Syntax_isNone(v___x_2922_);
                    if v___x_2923_ == 0 {
                        v___x_2924_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_2922_);
                        v___x_2925_ = l_Lean_Syntax_matchesNull(v___x_2922_, v___x_2924_);
                        if v___x_2925_ == 0 {
                            lean_dec(v___x_2922_);
                            lean_dec(v_stx_1648_);
                            v___x_2926_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1650_);
                            return v___x_2926_;
                        } else {
                            v_doc_x3f_2927_ = l_Lean_Syntax_getArg(v___x_2922_, v___x_1926_);
                            lean_dec(v___x_2922_);
                            v___x_2928_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__54;
                            lean_inc(v_doc_x3f_2927_);
                            v___x_2929_ = l_Lean_Syntax_isOfKind(v_doc_x3f_2927_, v___x_2928_);
                            if v___x_2929_ == 0 {
                                lean_dec(v_doc_x3f_2927_);
                                lean_dec(v_stx_1648_);
                                v___x_2930_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1650_);
                                return v___x_2930_;
                            } else {
                                v___x_2931_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2931_, 0, v_doc_x3f_2927_);
                                v_doc_x3f_2906_ = v___x_2931_;
                                v___y_2907_ = v___y_1649_;
                                v___y_2908_ = v___y_1650_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2922_);
                        v___x_2932_ = lean_box(0);
                        v_doc_x3f_2906_ = v___x_2932_;
                        v___y_2907_ = v___y_1649_;
                        v___y_2908_ = v___y_1650_;
                        state = 38;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_1668_);
                v___x_1671_ = l_Array_append___redArg(v___y_1668_, v___y_1670_);
                lean_dec_ref(v___y_1670_);
                lean_inc_n(v___y_1655_, 3);
                lean_inc_n(v___y_1654_, 7);
                v___x_1672_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1672_, 0, v___y_1654_);
                lean_ctor_set(v___x_1672_, 1, v___y_1655_);
                lean_ctor_set(v___x_1672_, 2, v___x_1671_);
                v___x_1673_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1674_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6,
                );
                v___x_1675_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__7;
                lean_inc(v___y_1665_);
                lean_inc(v___y_1656_);
                v___x_1676_ = l_Lean_addMacroScope(v___y_1656_, v___x_1675_, v___y_1665_);
                v___x_1677_ = lean_box(0);
                v___x_1678_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1678_, 0, v___y_1654_);
                lean_ctor_set(v___x_1678_, 1, v___x_1674_);
                lean_ctor_set(v___x_1678_, 2, v___x_1676_);
                lean_ctor_set(v___x_1678_, 3, v___x_1677_);
                lean_inc(v___y_1664_);
                lean_inc_ref(v___x_1678_);
                v___x_1679_ =
                    l_Lean_Syntax_node2(v___y_1654_, v___x_1673_, v___x_1678_, v___y_1664_);
                v___x_1680_ =
                    l_Lean_Syntax_node2(v___y_1654_, v___y_1655_, v___x_1679_, v___y_1660_);
                v___x_1681_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1682_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1682_, 0, v___y_1654_);
                lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                v___x_1683_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                lean_inc_ref(v___y_1657_);
                v___x_1684_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1657_, v___x_1683_);
                v___x_1685_ = l_Lean_Syntax_node1(v___y_1654_, v___y_1655_, v___x_1678_);
                v___x_1686_ =
                    l_Lean_Syntax_node2(v___y_1654_, v___x_1684_, v___y_1666_, v___x_1685_);
                v___x_1687_ = lean_unsigned_to_nat(10);
                v___x_1688_ = lean_mk_empty_array_with_capacity(v___x_1687_);
                v___x_1689_ = lean_array_push(v___x_1688_, v___y_1662_);
                v___x_1690_ = lean_array_push(v___x_1689_, v___y_1667_);
                v___x_1691_ = lean_array_push(v___x_1690_, v___y_1669_);
                v___x_1692_ = lean_array_push(v___x_1691_, v___y_1659_);
                v___x_1693_ = lean_array_push(v___x_1692_, v___y_1664_);
                v___x_1694_ = lean_array_push(v___x_1693_, v___y_1658_);
                v___x_1695_ = lean_array_push(v___x_1694_, v___x_1672_);
                v___x_1696_ = lean_array_push(v___x_1695_, v___x_1680_);
                v___x_1697_ = lean_array_push(v___x_1696_, v___x_1682_);
                v___x_1698_ = lean_array_push(v___x_1697_, v___x_1686_);
                lean_inc(v___y_1663_);
                v___x_1699_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1699_, 0, v___y_1654_);
                lean_ctor_set(v___x_1699_, 1, v___y_1663_);
                lean_ctor_set(v___x_1699_, 2, v___x_1698_);
                v___x_1700_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1700_, 0, v___x_1699_);
                lean_ctor_set(v___x_1700_, 1, v___y_1661_);
                return v___x_1700_;
            }
            2 => {
                lean_inc_ref(v___y_1702_);
                v___x_1719_ = l_Array_append___redArg(v___y_1702_, v___y_1718_);
                lean_dec_ref(v___y_1718_);
                lean_inc_n(v___y_1711_, 3);
                lean_inc_n(v___y_1715_, 7);
                v___x_1720_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1720_, 0, v___y_1715_);
                lean_ctor_set(v___x_1720_, 1, v___y_1711_);
                lean_ctor_set(v___x_1720_, 2, v___x_1719_);
                v___x_1721_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1722_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__6,
                );
                v___x_1723_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__7;
                lean_inc(v___y_1712_);
                lean_inc(v___y_1703_);
                v___x_1724_ = l_Lean_addMacroScope(v___y_1703_, v___x_1723_, v___y_1712_);
                v___x_1725_ = lean_box(0);
                v___x_1726_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1726_, 0, v___y_1715_);
                lean_ctor_set(v___x_1726_, 1, v___x_1722_);
                lean_ctor_set(v___x_1726_, 2, v___x_1724_);
                lean_ctor_set(v___x_1726_, 3, v___x_1725_);
                lean_inc(v___y_1707_);
                lean_inc_ref(v___x_1726_);
                v___x_1727_ =
                    l_Lean_Syntax_node2(v___y_1715_, v___x_1721_, v___x_1726_, v___y_1707_);
                v___x_1728_ =
                    l_Lean_Syntax_node2(v___y_1715_, v___y_1711_, v___y_1704_, v___x_1727_);
                v___x_1729_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1730_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1730_, 0, v___y_1715_);
                lean_ctor_set(v___x_1730_, 1, v___x_1729_);
                v___x_1731_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                lean_inc_ref(v___y_1709_);
                v___x_1732_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1709_, v___x_1731_);
                v___x_1733_ = l_Lean_Syntax_node1(v___y_1715_, v___y_1711_, v___x_1726_);
                v___x_1734_ =
                    l_Lean_Syntax_node2(v___y_1715_, v___x_1732_, v___y_1706_, v___x_1733_);
                v___x_1735_ = lean_unsigned_to_nat(10);
                v___x_1736_ = lean_mk_empty_array_with_capacity(v___x_1735_);
                v___x_1737_ = lean_array_push(v___x_1736_, v___y_1708_);
                v___x_1738_ = lean_array_push(v___x_1737_, v___y_1710_);
                v___x_1739_ = lean_array_push(v___x_1738_, v___y_1717_);
                v___x_1740_ = lean_array_push(v___x_1739_, v___y_1716_);
                v___x_1741_ = lean_array_push(v___x_1740_, v___y_1707_);
                v___x_1742_ = lean_array_push(v___x_1741_, v___y_1705_);
                v___x_1743_ = lean_array_push(v___x_1742_, v___x_1720_);
                v___x_1744_ = lean_array_push(v___x_1743_, v___x_1728_);
                v___x_1745_ = lean_array_push(v___x_1744_, v___x_1730_);
                v___x_1746_ = lean_array_push(v___x_1745_, v___x_1734_);
                lean_inc(v___y_1714_);
                v___x_1747_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1747_, 0, v___y_1715_);
                lean_ctor_set(v___x_1747_, 1, v___y_1714_);
                lean_ctor_set(v___x_1747_, 2, v___x_1746_);
                v___x_1748_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1748_, 0, v___x_1747_);
                lean_ctor_set(v___x_1748_, 1, v___y_1713_);
                return v___x_1748_;
            }
            3 => {
                lean_inc_ref(v___y_1752_);
                v___x_1770_ = l_Array_append___redArg(v___y_1752_, v___y_1769_);
                lean_dec_ref(v___y_1769_);
                lean_inc_n(v___y_1751_, 4);
                lean_inc_n(v___y_1758_, 11);
                v___x_1771_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1771_, 0, v___y_1758_);
                lean_ctor_set(v___x_1771_, 1, v___y_1751_);
                lean_ctor_set(v___x_1771_, 2, v___x_1770_);
                v___x_1772_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1773_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11,
                );
                v___x_1774_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
                lean_inc_n(v___y_1764_, 2);
                lean_inc_n(v___y_1750_, 2);
                v___x_1775_ = l_Lean_addMacroScope(v___y_1750_, v___x_1774_, v___y_1764_);
                v___x_1776_ = lean_box(0);
                v___x_1777_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1777_, 0, v___y_1758_);
                lean_ctor_set(v___x_1777_, 1, v___x_1773_);
                lean_ctor_set(v___x_1777_, 2, v___x_1775_);
                lean_ctor_set(v___x_1777_, 3, v___x_1776_);
                lean_inc(v___y_1756_);
                v___x_1778_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___y_1756_, v___y_1754_, v___y_1765_);
                v___x_1779_ = l_Lean_Syntax_node1(v___y_1758_, v___y_1751_, v___x_1778_);
                lean_inc_ref(v___x_1777_);
                v___x_1780_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___x_1772_, v___x_1777_, v___x_1779_);
                v___x_1781_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14,
                );
                v___x_1782_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
                v___x_1783_ = l_Lean_addMacroScope(v___y_1750_, v___x_1782_, v___y_1764_);
                v___x_1784_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1784_, 0, v___y_1758_);
                lean_ctor_set(v___x_1784_, 1, v___x_1781_);
                lean_ctor_set(v___x_1784_, 2, v___x_1783_);
                lean_ctor_set(v___x_1784_, 3, v___x_1776_);
                lean_inc(v___y_1755_);
                lean_inc_ref(v___x_1784_);
                v___x_1785_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___x_1772_, v___x_1784_, v___y_1755_);
                v___x_1786_ = l_Lean_Syntax_node3(
                    v___y_1758_,
                    v___y_1751_,
                    v___x_1780_,
                    v___y_1768_,
                    v___x_1785_,
                );
                v___x_1787_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1788_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1788_, 0, v___y_1758_);
                lean_ctor_set(v___x_1788_, 1, v___x_1787_);
                v___x_1789_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                lean_inc_ref(v___y_1759_);
                v___x_1790_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1759_, v___x_1789_);
                v___x_1791_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___y_1751_, v___x_1777_, v___x_1784_);
                v___x_1792_ =
                    l_Lean_Syntax_node2(v___y_1758_, v___x_1790_, v___y_1753_, v___x_1791_);
                v___x_1793_ = lean_unsigned_to_nat(10);
                v___x_1794_ = lean_mk_empty_array_with_capacity(v___x_1793_);
                v___x_1795_ = lean_array_push(v___x_1794_, v___y_1766_);
                v___x_1796_ = lean_array_push(v___x_1795_, v___y_1762_);
                v___x_1797_ = lean_array_push(v___x_1796_, v___y_1763_);
                v___x_1798_ = lean_array_push(v___x_1797_, v___y_1760_);
                v___x_1799_ = lean_array_push(v___x_1798_, v___y_1755_);
                v___x_1800_ = lean_array_push(v___x_1799_, v___y_1761_);
                v___x_1801_ = lean_array_push(v___x_1800_, v___x_1771_);
                v___x_1802_ = lean_array_push(v___x_1801_, v___x_1786_);
                v___x_1803_ = lean_array_push(v___x_1802_, v___x_1788_);
                v___x_1804_ = lean_array_push(v___x_1803_, v___x_1792_);
                lean_inc(v___y_1757_);
                v___x_1805_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1805_, 0, v___y_1758_);
                lean_ctor_set(v___x_1805_, 1, v___y_1757_);
                lean_ctor_set(v___x_1805_, 2, v___x_1804_);
                v___x_1806_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1806_, 0, v___x_1805_);
                lean_ctor_set(v___x_1806_, 1, v___y_1767_);
                return v___x_1806_;
            }
            4 => {
                lean_inc_ref(v___y_1826_);
                v___x_1828_ = l_Array_append___redArg(v___y_1826_, v___y_1827_);
                lean_dec_ref(v___y_1827_);
                lean_inc_n(v___y_1809_, 4);
                lean_inc_n(v___y_1813_, 11);
                v___x_1829_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1829_, 0, v___y_1813_);
                lean_ctor_set(v___x_1829_, 1, v___y_1809_);
                lean_ctor_set(v___x_1829_, 2, v___x_1828_);
                v___x_1830_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1831_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11,
                );
                v___x_1832_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
                lean_inc_n(v___y_1821_, 2);
                lean_inc_n(v___y_1820_, 2);
                v___x_1833_ = l_Lean_addMacroScope(v___y_1820_, v___x_1832_, v___y_1821_);
                v___x_1834_ = lean_box(0);
                v___x_1835_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1835_, 0, v___y_1813_);
                lean_ctor_set(v___x_1835_, 1, v___x_1831_);
                lean_ctor_set(v___x_1835_, 2, v___x_1833_);
                lean_ctor_set(v___x_1835_, 3, v___x_1834_);
                lean_inc(v___y_1819_);
                v___x_1836_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___y_1819_, v___y_1808_, v___y_1822_);
                v___x_1837_ = l_Lean_Syntax_node1(v___y_1813_, v___y_1809_, v___x_1836_);
                lean_inc(v___x_1837_);
                lean_inc_ref(v___x_1835_);
                v___x_1838_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___x_1830_, v___x_1835_, v___x_1837_);
                v___x_1839_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14,
                );
                v___x_1840_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
                v___x_1841_ = l_Lean_addMacroScope(v___y_1820_, v___x_1840_, v___y_1821_);
                v___x_1842_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1842_, 0, v___y_1813_);
                lean_ctor_set(v___x_1842_, 1, v___x_1839_);
                lean_ctor_set(v___x_1842_, 2, v___x_1841_);
                lean_ctor_set(v___x_1842_, 3, v___x_1834_);
                lean_inc_ref(v___x_1842_);
                v___x_1843_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___x_1830_, v___x_1842_, v___x_1837_);
                v___x_1844_ = l_Lean_Syntax_node3(
                    v___y_1813_,
                    v___y_1809_,
                    v___x_1838_,
                    v___y_1823_,
                    v___x_1843_,
                );
                v___x_1845_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1846_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1846_, 0, v___y_1813_);
                lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                v___x_1847_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                lean_inc_ref(v___y_1817_);
                v___x_1848_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1817_, v___x_1847_);
                v___x_1849_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___y_1809_, v___x_1835_, v___x_1842_);
                v___x_1850_ =
                    l_Lean_Syntax_node2(v___y_1813_, v___x_1848_, v___y_1810_, v___x_1849_);
                v___x_1851_ = lean_unsigned_to_nat(10);
                v___x_1852_ = lean_mk_empty_array_with_capacity(v___x_1851_);
                v___x_1853_ = lean_array_push(v___x_1852_, v___y_1818_);
                v___x_1854_ = lean_array_push(v___x_1853_, v___y_1825_);
                v___x_1855_ = lean_array_push(v___x_1854_, v___y_1812_);
                v___x_1856_ = lean_array_push(v___x_1855_, v___y_1815_);
                v___x_1857_ = lean_array_push(v___x_1856_, v___y_1814_);
                v___x_1858_ = lean_array_push(v___x_1857_, v___y_1816_);
                v___x_1859_ = lean_array_push(v___x_1858_, v___x_1829_);
                v___x_1860_ = lean_array_push(v___x_1859_, v___x_1844_);
                v___x_1861_ = lean_array_push(v___x_1860_, v___x_1846_);
                v___x_1862_ = lean_array_push(v___x_1861_, v___x_1850_);
                lean_inc(v___y_1824_);
                v___x_1863_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1863_, 0, v___y_1813_);
                lean_ctor_set(v___x_1863_, 1, v___y_1824_);
                lean_ctor_set(v___x_1863_, 2, v___x_1862_);
                v___x_1864_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1864_, 0, v___x_1863_);
                lean_ctor_set(v___x_1864_, 1, v___y_1811_);
                return v___x_1864_;
            }
            5 => {
                lean_inc_ref(v___y_1879_);
                v___x_1886_ = l_Array_append___redArg(v___y_1879_, v___y_1885_);
                lean_dec_ref(v___y_1885_);
                lean_inc_n(v___y_1876_, 4);
                lean_inc_n(v___y_1882_, 11);
                v___x_1887_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1887_, 0, v___y_1882_);
                lean_ctor_set(v___x_1887_, 1, v___y_1876_);
                lean_ctor_set(v___x_1887_, 2, v___x_1886_);
                v___x_1888_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__4;
                v___x_1889_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__11_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__11,
                );
                v___x_1890_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__12;
                lean_inc_n(v___y_1878_, 2);
                lean_inc_n(v___y_1884_, 2);
                v___x_1891_ = l_Lean_addMacroScope(v___y_1884_, v___x_1890_, v___y_1878_);
                v___x_1892_ = lean_box(0);
                v___x_1893_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1893_, 0, v___y_1882_);
                lean_ctor_set(v___x_1893_, 1, v___x_1889_);
                lean_ctor_set(v___x_1893_, 2, v___x_1891_);
                lean_ctor_set(v___x_1893_, 3, v___x_1892_);
                lean_inc(v___y_1877_);
                lean_inc_ref(v___x_1893_);
                v___x_1894_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___x_1888_, v___x_1893_, v___y_1877_);
                v___x_1895_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__14_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__14,
                );
                v___x_1896_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__15;
                v___x_1897_ = l_Lean_addMacroScope(v___y_1884_, v___x_1896_, v___y_1878_);
                v___x_1898_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1898_, 0, v___y_1882_);
                lean_ctor_set(v___x_1898_, 1, v___x_1895_);
                lean_ctor_set(v___x_1898_, 2, v___x_1897_);
                lean_ctor_set(v___x_1898_, 3, v___x_1892_);
                lean_inc(v___y_1874_);
                v___x_1899_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___y_1874_, v___y_1867_, v___y_1880_);
                v___x_1900_ = l_Lean_Syntax_node1(v___y_1882_, v___y_1876_, v___x_1899_);
                lean_inc_ref(v___x_1898_);
                v___x_1901_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___x_1888_, v___x_1898_, v___x_1900_);
                v___x_1902_ = l_Lean_Syntax_node3(
                    v___y_1882_,
                    v___y_1876_,
                    v___x_1894_,
                    v___y_1868_,
                    v___x_1901_,
                );
                v___x_1903_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__8;
                v___x_1904_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1904_, 0, v___y_1882_);
                lean_ctor_set(v___x_1904_, 1, v___x_1903_);
                v___x_1905_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__9;
                lean_inc_ref(v___y_1875_);
                v___x_1906_ =
                    l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_1875_, v___x_1905_);
                v___x_1907_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___y_1876_, v___x_1893_, v___x_1898_);
                v___x_1908_ =
                    l_Lean_Syntax_node2(v___y_1882_, v___x_1906_, v___y_1869_, v___x_1907_);
                v___x_1909_ = lean_unsigned_to_nat(10);
                v___x_1910_ = lean_mk_empty_array_with_capacity(v___x_1909_);
                v___x_1911_ = lean_array_push(v___x_1910_, v___y_1873_);
                v___x_1912_ = lean_array_push(v___x_1911_, v___y_1883_);
                v___x_1913_ = lean_array_push(v___x_1912_, v___y_1866_);
                v___x_1914_ = lean_array_push(v___x_1913_, v___y_1881_);
                v___x_1915_ = lean_array_push(v___x_1914_, v___y_1877_);
                v___x_1916_ = lean_array_push(v___x_1915_, v___y_1870_);
                v___x_1917_ = lean_array_push(v___x_1916_, v___x_1887_);
                v___x_1918_ = lean_array_push(v___x_1917_, v___x_1902_);
                v___x_1919_ = lean_array_push(v___x_1918_, v___x_1904_);
                v___x_1920_ = lean_array_push(v___x_1919_, v___x_1908_);
                lean_inc(v___y_1871_);
                v___x_1921_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1921_, 0, v___y_1882_);
                lean_ctor_set(v___x_1921_, 1, v___y_1871_);
                lean_ctor_set(v___x_1921_, 2, v___x_1920_);
                v___x_1922_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1922_, 0, v___x_1921_);
                lean_ctor_set(v___x_1922_, 1, v___y_1872_);
                return v___x_1922_;
            }
            6 => {
                lean_inc_ref(v___y_1942_);
                v___x_1945_ = l_Array_append___redArg(v___y_1942_, v___y_1944_);
                lean_dec_ref(v___y_1944_);
                lean_inc(v___y_1929_);
                lean_inc(v___y_1928_);
                v___x_1946_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1946_, 0, v___y_1928_);
                lean_ctor_set(v___x_1946_, 1, v___y_1929_);
                lean_ctor_set(v___x_1946_, 2, v___x_1945_);
                if lean_obj_tag(v___y_1932_) == 1 {
                    v_val_1947_ = lean_ctor_get(v___y_1932_, 0);
                    lean_inc(v_val_1947_);
                    lean_dec_ref_known(v___y_1932_, 1);
                    v___x_1948_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_1949_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_1928_, 5);
                    v___x_1950_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1950_, 0, v___y_1928_);
                    lean_ctor_set(v___x_1950_, 1, v___x_1949_);
                    v___x_1951_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_1952_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1952_, 0, v___y_1928_);
                    lean_ctor_set(v___x_1952_, 1, v___x_1951_);
                    v___x_1953_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_1954_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1954_, 0, v___y_1928_);
                    lean_ctor_set(v___x_1954_, 1, v___x_1953_);
                    v___x_1955_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_1956_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1956_, 0, v___y_1928_);
                    lean_ctor_set(v___x_1956_, 1, v___x_1955_);
                    v___x_1957_ = l_Lean_Syntax_node5(
                        v___y_1928_,
                        v___x_1948_,
                        v___x_1950_,
                        v___x_1952_,
                        v___x_1954_,
                        v_val_1947_,
                        v___x_1956_,
                    );
                    v___x_1958_ = l_Array_mkArray1___redArg(v___x_1957_);
                    v___y_1654_ = v___y_1928_;
                    v___y_1655_ = v___y_1929_;
                    v___y_1656_ = v___y_1930_;
                    v___y_1657_ = v___y_1931_;
                    v___y_1658_ = v___x_1946_;
                    v___y_1659_ = v___y_1933_;
                    v___y_1660_ = v___y_1934_;
                    v___y_1661_ = v___y_1935_;
                    v___y_1662_ = v___y_1936_;
                    v___y_1663_ = v___y_1937_;
                    v___y_1664_ = v___y_1938_;
                    v___y_1665_ = v___y_1940_;
                    v___y_1666_ = v___y_1941_;
                    v___y_1667_ = v___y_1939_;
                    v___y_1668_ = v___y_1942_;
                    v___y_1669_ = v___y_1943_;
                    v___y_1670_ = v___x_1958_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1932_);
                    v___x_1959_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1654_ = v___y_1928_;
                    v___y_1655_ = v___y_1929_;
                    v___y_1656_ = v___y_1930_;
                    v___y_1657_ = v___y_1931_;
                    v___y_1658_ = v___x_1946_;
                    v___y_1659_ = v___y_1933_;
                    v___y_1660_ = v___y_1934_;
                    v___y_1661_ = v___y_1935_;
                    v___y_1662_ = v___y_1936_;
                    v___y_1663_ = v___y_1937_;
                    v___y_1664_ = v___y_1938_;
                    v___y_1665_ = v___y_1940_;
                    v___y_1666_ = v___y_1941_;
                    v___y_1667_ = v___y_1939_;
                    v___y_1668_ = v___y_1942_;
                    v___y_1669_ = v___y_1943_;
                    v___y_1670_ = v___x_1959_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                lean_inc_ref_n(v___y_1975_, 2);
                v___x_1979_ = l_Array_append___redArg(v___y_1975_, v___y_1978_);
                lean_dec_ref(v___y_1978_);
                lean_inc_n(v___y_1964_, 3);
                lean_inc_n(v___y_1962_, 7);
                v___x_1980_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1980_, 0, v___y_1962_);
                lean_ctor_set(v___x_1980_, 1, v___y_1964_);
                lean_ctor_set(v___x_1980_, 2, v___x_1979_);
                v___x_1981_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1981_, 0, v___y_1962_);
                lean_ctor_set(v___x_1981_, 1, v___y_1964_);
                lean_ctor_set(v___x_1981_, 2, v___y_1975_);
                lean_inc(v___y_1961_);
                v___x_1982_ = l_Lean_Syntax_node1(v___y_1962_, v___y_1961_, v___x_1981_);
                lean_inc_ref(v___y_1963_);
                v___x_1983_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1983_, 0, v___y_1962_);
                lean_ctor_set(v___x_1983_, 1, v___y_1963_);
                v___x_1984_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_1985_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1985_, 0, v___y_1962_);
                lean_ctor_set(v___x_1985_, 1, v___x_1984_);
                lean_inc(v___y_1976_);
                v___x_1986_ =
                    l_Lean_Syntax_node2(v___y_1962_, v___y_1976_, v___x_1985_, v___y_1977_);
                v___x_1987_ = l_Lean_Syntax_node1(v___y_1962_, v___y_1964_, v___x_1986_);
                if lean_obj_tag(v___y_1971_) == 1 {
                    v_val_1988_ = lean_ctor_get(v___y_1971_, 0);
                    lean_inc(v_val_1988_);
                    lean_dec_ref_known(v___y_1971_, 1);
                    v___x_1989_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_1990_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_1962_, 5);
                    v___x_1991_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1991_, 0, v___y_1962_);
                    lean_ctor_set(v___x_1991_, 1, v___x_1990_);
                    v___x_1992_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_1993_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1993_, 0, v___y_1962_);
                    lean_ctor_set(v___x_1993_, 1, v___x_1992_);
                    v___x_1994_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_1995_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1995_, 0, v___y_1962_);
                    lean_ctor_set(v___x_1995_, 1, v___x_1994_);
                    v___x_1996_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_1997_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_1997_, 0, v___y_1962_);
                    lean_ctor_set(v___x_1997_, 1, v___x_1996_);
                    v___x_1998_ = l_Lean_Syntax_node5(
                        v___y_1962_,
                        v___x_1989_,
                        v___x_1991_,
                        v___x_1993_,
                        v___x_1995_,
                        v_val_1988_,
                        v___x_1997_,
                    );
                    v___x_1999_ = l_Array_mkArray1___redArg(v___x_1998_);
                    v___y_1928_ = v___y_1962_;
                    v___y_1929_ = v___y_1964_;
                    v___y_1930_ = v___y_1965_;
                    v___y_1931_ = v___y_1966_;
                    v___y_1932_ = v___y_1967_;
                    v___y_1933_ = v___x_1983_;
                    v___y_1934_ = v___y_1968_;
                    v___y_1935_ = v___y_1969_;
                    v___y_1936_ = v___y_1970_;
                    v___y_1937_ = v___y_1972_;
                    v___y_1938_ = v___x_1987_;
                    v___y_1939_ = v___x_1980_;
                    v___y_1940_ = v___y_1974_;
                    v___y_1941_ = v___y_1973_;
                    v___y_1942_ = v___y_1975_;
                    v___y_1943_ = v___x_1982_;
                    v___y_1944_ = v___x_1999_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v___y_1971_);
                    v___x_2000_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1928_ = v___y_1962_;
                    v___y_1929_ = v___y_1964_;
                    v___y_1930_ = v___y_1965_;
                    v___y_1931_ = v___y_1966_;
                    v___y_1932_ = v___y_1967_;
                    v___y_1933_ = v___x_1983_;
                    v___y_1934_ = v___y_1968_;
                    v___y_1935_ = v___y_1969_;
                    v___y_1936_ = v___y_1970_;
                    v___y_1937_ = v___y_1972_;
                    v___y_1938_ = v___x_1987_;
                    v___y_1939_ = v___x_1980_;
                    v___y_1940_ = v___y_1974_;
                    v___y_1941_ = v___y_1973_;
                    v___y_1942_ = v___y_1975_;
                    v___y_1943_ = v___x_1982_;
                    v___y_1944_ = v___x_2000_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v___y_2017_);
                v___x_2020_ = l_Array_append___redArg(v___y_2017_, v___y_2019_);
                lean_dec_ref(v___y_2019_);
                lean_inc(v___y_2005_);
                lean_inc(v___y_2003_);
                v___x_2021_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2021_, 0, v___y_2003_);
                lean_ctor_set(v___x_2021_, 1, v___y_2005_);
                lean_ctor_set(v___x_2021_, 2, v___x_2020_);
                if lean_obj_tag(v___y_2006_) == 1 {
                    v_val_2022_ = lean_ctor_get(v___y_2006_, 0);
                    lean_inc(v_val_2022_);
                    lean_dec_ref_known(v___y_2006_, 1);
                    v___x_2023_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    lean_inc_ref(v___y_2008_);
                    v___x_2024_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2008_, v___x_2023_);
                    v___x_2025_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    lean_inc_n(v___y_2003_, 4);
                    v___x_2026_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2026_, 0, v___y_2003_);
                    lean_ctor_set(v___x_2026_, 1, v___x_2025_);
                    lean_inc_ref(v___y_2017_);
                    v___x_2027_ = l_Array_append___redArg(v___y_2017_, v_val_2022_);
                    lean_dec(v_val_2022_);
                    lean_inc(v___y_2005_);
                    v___x_2028_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2028_, 0, v___y_2003_);
                    lean_ctor_set(v___x_2028_, 1, v___y_2005_);
                    lean_ctor_set(v___x_2028_, 2, v___x_2027_);
                    v___x_2029_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2030_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2030_, 0, v___y_2003_);
                    lean_ctor_set(v___x_2030_, 1, v___x_2029_);
                    v___x_2031_ = l_Lean_Syntax_node3(
                        v___y_2003_,
                        v___x_2024_,
                        v___x_2026_,
                        v___x_2028_,
                        v___x_2030_,
                    );
                    v___x_2032_ = l_Array_mkArray1___redArg(v___x_2031_);
                    v___y_1961_ = v___y_2002_;
                    v___y_1962_ = v___y_2003_;
                    v___y_1963_ = v___y_2004_;
                    v___y_1964_ = v___y_2005_;
                    v___y_1965_ = v___y_2007_;
                    v___y_1966_ = v___y_2008_;
                    v___y_1967_ = v___y_2009_;
                    v___y_1968_ = v___y_2010_;
                    v___y_1969_ = v___y_2011_;
                    v___y_1970_ = v___x_2021_;
                    v___y_1971_ = v___y_2012_;
                    v___y_1972_ = v___y_2013_;
                    v___y_1973_ = v___y_2015_;
                    v___y_1974_ = v___y_2014_;
                    v___y_1975_ = v___y_2017_;
                    v___y_1976_ = v___y_2016_;
                    v___y_1977_ = v___y_2018_;
                    v___y_1978_ = v___x_2032_;
                    state = 7;
                    continue;
                } else {
                    lean_dec(v___y_2006_);
                    v___x_2033_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1961_ = v___y_2002_;
                    v___y_1962_ = v___y_2003_;
                    v___y_1963_ = v___y_2004_;
                    v___y_1964_ = v___y_2005_;
                    v___y_1965_ = v___y_2007_;
                    v___y_1966_ = v___y_2008_;
                    v___y_1967_ = v___y_2009_;
                    v___y_1968_ = v___y_2010_;
                    v___y_1969_ = v___y_2011_;
                    v___y_1970_ = v___x_2021_;
                    v___y_1971_ = v___y_2012_;
                    v___y_1972_ = v___y_2013_;
                    v___y_1973_ = v___y_2015_;
                    v___y_1974_ = v___y_2014_;
                    v___y_1975_ = v___y_2017_;
                    v___y_1976_ = v___y_2016_;
                    v___y_1977_ = v___y_2018_;
                    v___y_1978_ = v___x_2033_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v_quotContext_2046_ = lean_ctor_get(v___y_2044_, 1);
                v_currMacroScope_2047_ = lean_ctor_get(v___y_2044_, 2);
                v_ref_2048_ = lean_ctor_get(v___y_2044_, 5);
                v___x_2049_ = lean_unsigned_to_nat(7);
                v___x_2050_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2049_);
                v___x_2051_ = lean_unsigned_to_nat(9);
                v___x_2052_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2051_);
                lean_dec(v_stx_1648_);
                v___x_2053_ = l_Lean_SourceInfo_fromRef(v_ref_2048_, v___y_2037_);
                v___x_2054_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                v___x_2055_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                v___x_2056_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                v___x_2057_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                );
                if lean_obj_tag(v___y_2040_) == 1 {
                    v_val_2058_ = lean_ctor_get(v___y_2040_, 0);
                    lean_inc(v_val_2058_);
                    lean_dec_ref_known(v___y_2040_, 1);
                    v___x_2059_ = l_Array_mkArray1___redArg(v_val_2058_);
                    v___y_2002_ = v___y_2035_;
                    v___y_2003_ = v___x_2053_;
                    v___y_2004_ = v___x_2054_;
                    v___y_2005_ = v___x_2056_;
                    v___y_2006_ = v___y_2039_;
                    v___y_2007_ = v_quotContext_2046_;
                    v___y_2008_ = v___y_2041_;
                    v___y_2009_ = v_prio_2043_;
                    v___y_2010_ = v___x_2050_;
                    v___y_2011_ = v___y_2045_;
                    v___y_2012_ = v___y_2036_;
                    v___y_2013_ = v___x_2055_;
                    v___y_2014_ = v_currMacroScope_2047_;
                    v___y_2015_ = v___x_2052_;
                    v___y_2016_ = v___y_2038_;
                    v___y_2017_ = v___x_2057_;
                    v___y_2018_ = v___y_2042_;
                    v___y_2019_ = v___x_2059_;
                    state = 8;
                    continue;
                } else {
                    lean_dec(v___y_2040_);
                    v___x_2060_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2002_ = v___y_2035_;
                    v___y_2003_ = v___x_2053_;
                    v___y_2004_ = v___x_2054_;
                    v___y_2005_ = v___x_2056_;
                    v___y_2006_ = v___y_2039_;
                    v___y_2007_ = v_quotContext_2046_;
                    v___y_2008_ = v___y_2041_;
                    v___y_2009_ = v_prio_2043_;
                    v___y_2010_ = v___x_2050_;
                    v___y_2011_ = v___y_2045_;
                    v___y_2012_ = v___y_2036_;
                    v___y_2013_ = v___x_2055_;
                    v___y_2014_ = v_currMacroScope_2047_;
                    v___y_2015_ = v___x_2052_;
                    v___y_2016_ = v___y_2038_;
                    v___y_2017_ = v___x_2057_;
                    v___y_2018_ = v___y_2042_;
                    v___y_2019_ = v___x_2060_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_2074_ = lean_unsigned_to_nat(6);
                v___x_2075_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2074_);
                v___x_2076_ = l_Lean_Syntax_isNone(v___x_2075_);
                if v___x_2076_ == 0 {
                    lean_inc(v___x_2075_);
                    v___x_2077_ = l_Lean_Syntax_matchesNull(v___x_2075_, v___y_2062_);
                    if v___x_2077_ == 0 {
                        lean_dec(v___x_2075_);
                        lean_dec(v_name_2071_);
                        lean_dec(v___y_2070_);
                        lean_dec(v___y_2068_);
                        lean_dec(v___y_2065_);
                        lean_dec(v_stx_1648_);
                        v___x_2078_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2073_);
                        return v___x_2078_;
                    } else {
                        v___x_2079_ = l_Lean_Syntax_getArg(v___x_2075_, v___x_1926_);
                        lean_dec(v___x_2075_);
                        v___x_2080_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        lean_inc(v___x_2079_);
                        v___x_2081_ = l_Lean_Syntax_isOfKind(v___x_2079_, v___x_2080_);
                        if v___x_2081_ == 0 {
                            lean_dec(v___x_2079_);
                            lean_dec(v_name_2071_);
                            lean_dec(v___y_2070_);
                            lean_dec(v___y_2068_);
                            lean_dec(v___y_2065_);
                            lean_dec(v_stx_1648_);
                            v___x_2082_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2073_);
                            return v___x_2082_;
                        } else {
                            v_prio_2083_ = l_Lean_Syntax_getArg(v___x_2079_, v___y_2067_);
                            lean_dec(v___x_2079_);
                            v___x_2084_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2084_, 0, v_prio_2083_);
                            v___y_2035_ = v___y_2063_;
                            v___y_2036_ = v_name_2071_;
                            v___y_2037_ = v___y_2064_;
                            v___y_2038_ = v___y_2066_;
                            v___y_2039_ = v___y_2065_;
                            v___y_2040_ = v___y_2068_;
                            v___y_2041_ = v___y_2069_;
                            v___y_2042_ = v___y_2070_;
                            v_prio_2043_ = v___x_2084_;
                            v___y_2044_ = v___y_2072_;
                            v___y_2045_ = v___y_2073_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2075_);
                    v___x_2085_ = lean_box(0);
                    v___y_2035_ = v___y_2063_;
                    v___y_2036_ = v_name_2071_;
                    v___y_2037_ = v___y_2064_;
                    v___y_2038_ = v___y_2066_;
                    v___y_2039_ = v___y_2065_;
                    v___y_2040_ = v___y_2068_;
                    v___y_2041_ = v___y_2069_;
                    v___y_2042_ = v___y_2070_;
                    v_prio_2043_ = v___x_2085_;
                    v___y_2044_ = v___y_2072_;
                    v___y_2045_ = v___y_2073_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                lean_inc_ref(v___y_2088_);
                v___x_2104_ = l_Array_append___redArg(v___y_2088_, v___y_2103_);
                lean_dec_ref(v___y_2103_);
                lean_inc(v___y_2096_);
                lean_inc(v___y_2098_);
                v___x_2105_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2105_, 0, v___y_2098_);
                lean_ctor_set(v___x_2105_, 1, v___y_2096_);
                lean_ctor_set(v___x_2105_, 2, v___x_2104_);
                if lean_obj_tag(v___y_2087_) == 1 {
                    v_val_2106_ = lean_ctor_get(v___y_2087_, 0);
                    lean_inc(v_val_2106_);
                    lean_dec_ref_known(v___y_2087_, 1);
                    v___x_2107_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2108_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2098_, 5);
                    v___x_2109_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2109_, 0, v___y_2098_);
                    lean_ctor_set(v___x_2109_, 1, v___x_2108_);
                    v___x_2110_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2111_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2111_, 0, v___y_2098_);
                    lean_ctor_set(v___x_2111_, 1, v___x_2110_);
                    v___x_2112_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2113_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2113_, 0, v___y_2098_);
                    lean_ctor_set(v___x_2113_, 1, v___x_2112_);
                    v___x_2114_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2115_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2115_, 0, v___y_2098_);
                    lean_ctor_set(v___x_2115_, 1, v___x_2114_);
                    v___x_2116_ = l_Lean_Syntax_node5(
                        v___y_2098_,
                        v___x_2107_,
                        v___x_2109_,
                        v___x_2111_,
                        v___x_2113_,
                        v_val_2106_,
                        v___x_2115_,
                    );
                    v___x_2117_ = l_Array_mkArray1___redArg(v___x_2116_);
                    v___y_1702_ = v___y_2088_;
                    v___y_1703_ = v___y_2089_;
                    v___y_1704_ = v___y_2090_;
                    v___y_1705_ = v___x_2105_;
                    v___y_1706_ = v___y_2091_;
                    v___y_1707_ = v___y_2092_;
                    v___y_1708_ = v___y_2093_;
                    v___y_1709_ = v___y_2094_;
                    v___y_1710_ = v___y_2095_;
                    v___y_1711_ = v___y_2096_;
                    v___y_1712_ = v___y_2097_;
                    v___y_1713_ = v___y_2099_;
                    v___y_1714_ = v___y_2100_;
                    v___y_1715_ = v___y_2098_;
                    v___y_1716_ = v___y_2101_;
                    v___y_1717_ = v___y_2102_;
                    v___y_1718_ = v___x_2117_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___y_2087_);
                    v___x_2118_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1702_ = v___y_2088_;
                    v___y_1703_ = v___y_2089_;
                    v___y_1704_ = v___y_2090_;
                    v___y_1705_ = v___x_2105_;
                    v___y_1706_ = v___y_2091_;
                    v___y_1707_ = v___y_2092_;
                    v___y_1708_ = v___y_2093_;
                    v___y_1709_ = v___y_2094_;
                    v___y_1710_ = v___y_2095_;
                    v___y_1711_ = v___y_2096_;
                    v___y_1712_ = v___y_2097_;
                    v___y_1713_ = v___y_2099_;
                    v___y_1714_ = v___y_2100_;
                    v___y_1715_ = v___y_2098_;
                    v___y_1716_ = v___y_2101_;
                    v___y_1717_ = v___y_2102_;
                    v___y_1718_ = v___x_2118_;
                    state = 2;
                    continue;
                }
            }
            12 => {
                lean_inc_ref_n(v___y_2122_, 2);
                v___x_2138_ = l_Array_append___redArg(v___y_2122_, v___y_2137_);
                lean_dec_ref(v___y_2137_);
                lean_inc_n(v___y_2130_, 3);
                lean_inc_n(v___y_2135_, 7);
                v___x_2139_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2139_, 0, v___y_2135_);
                lean_ctor_set(v___x_2139_, 1, v___y_2130_);
                lean_ctor_set(v___x_2139_, 2, v___x_2138_);
                v___x_2140_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2140_, 0, v___y_2135_);
                lean_ctor_set(v___x_2140_, 1, v___y_2130_);
                lean_ctor_set(v___x_2140_, 2, v___y_2122_);
                lean_inc(v___y_2121_);
                v___x_2141_ = l_Lean_Syntax_node1(v___y_2135_, v___y_2121_, v___x_2140_);
                lean_inc_ref(v___y_2127_);
                v___x_2142_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2142_, 0, v___y_2135_);
                lean_ctor_set(v___x_2142_, 1, v___y_2127_);
                v___x_2143_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2144_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2144_, 0, v___y_2135_);
                lean_ctor_set(v___x_2144_, 1, v___x_2143_);
                lean_inc(v___y_2136_);
                v___x_2145_ =
                    l_Lean_Syntax_node2(v___y_2135_, v___y_2136_, v___x_2144_, v___y_2132_);
                v___x_2146_ = l_Lean_Syntax_node1(v___y_2135_, v___y_2130_, v___x_2145_);
                if lean_obj_tag(v___y_2120_) == 1 {
                    v_val_2147_ = lean_ctor_get(v___y_2120_, 0);
                    lean_inc(v_val_2147_);
                    lean_dec_ref_known(v___y_2120_, 1);
                    v___x_2148_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2149_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2135_, 5);
                    v___x_2150_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2150_, 0, v___y_2135_);
                    lean_ctor_set(v___x_2150_, 1, v___x_2149_);
                    v___x_2151_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2152_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2152_, 0, v___y_2135_);
                    lean_ctor_set(v___x_2152_, 1, v___x_2151_);
                    v___x_2153_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2154_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2154_, 0, v___y_2135_);
                    lean_ctor_set(v___x_2154_, 1, v___x_2153_);
                    v___x_2155_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2156_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2156_, 0, v___y_2135_);
                    lean_ctor_set(v___x_2156_, 1, v___x_2155_);
                    v___x_2157_ = l_Lean_Syntax_node5(
                        v___y_2135_,
                        v___x_2148_,
                        v___x_2150_,
                        v___x_2152_,
                        v___x_2154_,
                        v_val_2147_,
                        v___x_2156_,
                    );
                    v___x_2158_ = l_Array_mkArray1___redArg(v___x_2157_);
                    v___y_2087_ = v___y_2123_;
                    v___y_2088_ = v___y_2122_;
                    v___y_2089_ = v___y_2124_;
                    v___y_2090_ = v___y_2125_;
                    v___y_2091_ = v___y_2126_;
                    v___y_2092_ = v___x_2146_;
                    v___y_2093_ = v___y_2128_;
                    v___y_2094_ = v___y_2129_;
                    v___y_2095_ = v___x_2139_;
                    v___y_2096_ = v___y_2130_;
                    v___y_2097_ = v___y_2131_;
                    v___y_2098_ = v___y_2135_;
                    v___y_2099_ = v___y_2134_;
                    v___y_2100_ = v___y_2133_;
                    v___y_2101_ = v___x_2142_;
                    v___y_2102_ = v___x_2141_;
                    v___y_2103_ = v___x_2158_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v___y_2120_);
                    v___x_2159_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2087_ = v___y_2123_;
                    v___y_2088_ = v___y_2122_;
                    v___y_2089_ = v___y_2124_;
                    v___y_2090_ = v___y_2125_;
                    v___y_2091_ = v___y_2126_;
                    v___y_2092_ = v___x_2146_;
                    v___y_2093_ = v___y_2128_;
                    v___y_2094_ = v___y_2129_;
                    v___y_2095_ = v___x_2139_;
                    v___y_2096_ = v___y_2130_;
                    v___y_2097_ = v___y_2131_;
                    v___y_2098_ = v___y_2135_;
                    v___y_2099_ = v___y_2134_;
                    v___y_2100_ = v___y_2133_;
                    v___y_2101_ = v___x_2142_;
                    v___y_2102_ = v___x_2141_;
                    v___y_2103_ = v___x_2159_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                lean_inc_ref(v___y_2163_);
                v___x_2179_ = l_Array_append___redArg(v___y_2163_, v___y_2178_);
                lean_dec_ref(v___y_2178_);
                lean_inc(v___y_2171_);
                lean_inc(v___y_2176_);
                v___x_2180_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2180_, 0, v___y_2176_);
                lean_ctor_set(v___x_2180_, 1, v___y_2171_);
                lean_ctor_set(v___x_2180_, 2, v___x_2179_);
                if lean_obj_tag(v___y_2167_) == 1 {
                    v_val_2181_ = lean_ctor_get(v___y_2167_, 0);
                    lean_inc(v_val_2181_);
                    lean_dec_ref_known(v___y_2167_, 1);
                    v___x_2182_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    lean_inc_ref(v___y_2170_);
                    v___x_2183_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2170_, v___x_2182_);
                    v___x_2184_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    lean_inc_n(v___y_2176_, 4);
                    v___x_2185_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2185_, 0, v___y_2176_);
                    lean_ctor_set(v___x_2185_, 1, v___x_2184_);
                    lean_inc_ref(v___y_2163_);
                    v___x_2186_ = l_Array_append___redArg(v___y_2163_, v_val_2181_);
                    lean_dec(v_val_2181_);
                    lean_inc(v___y_2171_);
                    v___x_2187_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2187_, 0, v___y_2176_);
                    lean_ctor_set(v___x_2187_, 1, v___y_2171_);
                    lean_ctor_set(v___x_2187_, 2, v___x_2186_);
                    v___x_2188_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2189_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2189_, 0, v___y_2176_);
                    lean_ctor_set(v___x_2189_, 1, v___x_2188_);
                    v___x_2190_ = l_Lean_Syntax_node3(
                        v___y_2176_,
                        v___x_2183_,
                        v___x_2185_,
                        v___x_2187_,
                        v___x_2189_,
                    );
                    v___x_2191_ = l_Array_mkArray1___redArg(v___x_2190_);
                    v___y_2120_ = v___y_2161_;
                    v___y_2121_ = v___y_2162_;
                    v___y_2122_ = v___y_2163_;
                    v___y_2123_ = v___y_2164_;
                    v___y_2124_ = v___y_2165_;
                    v___y_2125_ = v___y_2166_;
                    v___y_2126_ = v___y_2168_;
                    v___y_2127_ = v___y_2169_;
                    v___y_2128_ = v___x_2180_;
                    v___y_2129_ = v___y_2170_;
                    v___y_2130_ = v___y_2171_;
                    v___y_2131_ = v___y_2172_;
                    v___y_2132_ = v___y_2173_;
                    v___y_2133_ = v___y_2175_;
                    v___y_2134_ = v___y_2174_;
                    v___y_2135_ = v___y_2176_;
                    v___y_2136_ = v___y_2177_;
                    v___y_2137_ = v___x_2191_;
                    state = 12;
                    continue;
                } else {
                    lean_dec(v___y_2167_);
                    v___x_2192_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2120_ = v___y_2161_;
                    v___y_2121_ = v___y_2162_;
                    v___y_2122_ = v___y_2163_;
                    v___y_2123_ = v___y_2164_;
                    v___y_2124_ = v___y_2165_;
                    v___y_2125_ = v___y_2166_;
                    v___y_2126_ = v___y_2168_;
                    v___y_2127_ = v___y_2169_;
                    v___y_2128_ = v___x_2180_;
                    v___y_2129_ = v___y_2170_;
                    v___y_2130_ = v___y_2171_;
                    v___y_2131_ = v___y_2172_;
                    v___y_2132_ = v___y_2173_;
                    v___y_2133_ = v___y_2175_;
                    v___y_2134_ = v___y_2174_;
                    v___y_2135_ = v___y_2176_;
                    v___y_2136_ = v___y_2177_;
                    v___y_2137_ = v___x_2192_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v_quotContext_2205_ = lean_ctor_get(v___y_2203_, 1);
                v_currMacroScope_2206_ = lean_ctor_get(v___y_2203_, 2);
                v_ref_2207_ = lean_ctor_get(v___y_2203_, 5);
                v___x_2208_ = lean_unsigned_to_nat(7);
                v___x_2209_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2208_);
                v___x_2210_ = lean_unsigned_to_nat(9);
                v___x_2211_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2210_);
                lean_dec(v_stx_1648_);
                v___x_2212_ = l_Lean_SourceInfo_fromRef(v_ref_2207_, v___y_2198_);
                v___x_2213_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                v___x_2214_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                v___x_2215_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                v___x_2216_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_expandMixfix___lam__0___closed__36),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                    ),
                    _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                );
                if lean_obj_tag(v___y_2199_) == 1 {
                    v_val_2217_ = lean_ctor_get(v___y_2199_, 0);
                    lean_inc(v_val_2217_);
                    lean_dec_ref_known(v___y_2199_, 1);
                    v___x_2218_ = l_Array_mkArray1___redArg(v_val_2217_);
                    v___y_2161_ = v___y_2194_;
                    v___y_2162_ = v___y_2195_;
                    v___y_2163_ = v___x_2216_;
                    v___y_2164_ = v_prio_2202_;
                    v___y_2165_ = v_quotContext_2205_;
                    v___y_2166_ = v___x_2209_;
                    v___y_2167_ = v___y_2197_;
                    v___y_2168_ = v___x_2211_;
                    v___y_2169_ = v___x_2213_;
                    v___y_2170_ = v___y_2200_;
                    v___y_2171_ = v___x_2215_;
                    v___y_2172_ = v_currMacroScope_2206_;
                    v___y_2173_ = v___y_2196_;
                    v___y_2174_ = v___y_2204_;
                    v___y_2175_ = v___x_2214_;
                    v___y_2176_ = v___x_2212_;
                    v___y_2177_ = v___y_2201_;
                    v___y_2178_ = v___x_2218_;
                    state = 13;
                    continue;
                } else {
                    lean_dec(v___y_2199_);
                    v___x_2219_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2161_ = v___y_2194_;
                    v___y_2162_ = v___y_2195_;
                    v___y_2163_ = v___x_2216_;
                    v___y_2164_ = v_prio_2202_;
                    v___y_2165_ = v_quotContext_2205_;
                    v___y_2166_ = v___x_2209_;
                    v___y_2167_ = v___y_2197_;
                    v___y_2168_ = v___x_2211_;
                    v___y_2169_ = v___x_2213_;
                    v___y_2170_ = v___y_2200_;
                    v___y_2171_ = v___x_2215_;
                    v___y_2172_ = v_currMacroScope_2206_;
                    v___y_2173_ = v___y_2196_;
                    v___y_2174_ = v___y_2204_;
                    v___y_2175_ = v___x_2214_;
                    v___y_2176_ = v___x_2212_;
                    v___y_2177_ = v___y_2201_;
                    v___y_2178_ = v___x_2219_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_2233_ = lean_unsigned_to_nat(6);
                v___x_2234_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2233_);
                v___x_2235_ = l_Lean_Syntax_isNone(v___x_2234_);
                if v___x_2235_ == 0 {
                    lean_inc(v___x_2234_);
                    v___x_2236_ = l_Lean_Syntax_matchesNull(v___x_2234_, v___y_2221_);
                    if v___x_2236_ == 0 {
                        lean_dec(v___x_2234_);
                        lean_dec(v_name_2230_);
                        lean_dec(v___y_2227_);
                        lean_dec(v___y_2224_);
                        lean_dec(v___y_2223_);
                        lean_dec(v_stx_1648_);
                        v___x_2237_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2232_);
                        return v___x_2237_;
                    } else {
                        v___x_2238_ = l_Lean_Syntax_getArg(v___x_2234_, v___x_1926_);
                        lean_dec(v___x_2234_);
                        v___x_2239_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        lean_inc(v___x_2238_);
                        v___x_2240_ = l_Lean_Syntax_isOfKind(v___x_2238_, v___x_2239_);
                        if v___x_2240_ == 0 {
                            lean_dec(v___x_2238_);
                            lean_dec(v_name_2230_);
                            lean_dec(v___y_2227_);
                            lean_dec(v___y_2224_);
                            lean_dec(v___y_2223_);
                            lean_dec(v_stx_1648_);
                            v___x_2241_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2232_);
                            return v___x_2241_;
                        } else {
                            v_prio_2242_ = l_Lean_Syntax_getArg(v___x_2238_, v___y_2226_);
                            lean_dec(v___x_2238_);
                            v___x_2243_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2243_, 0, v_prio_2242_);
                            v___y_2194_ = v_name_2230_;
                            v___y_2195_ = v___y_2222_;
                            v___y_2196_ = v___y_2223_;
                            v___y_2197_ = v___y_2224_;
                            v___y_2198_ = v___y_2225_;
                            v___y_2199_ = v___y_2227_;
                            v___y_2200_ = v___y_2228_;
                            v___y_2201_ = v___y_2229_;
                            v_prio_2202_ = v___x_2243_;
                            v___y_2203_ = v___y_2231_;
                            v___y_2204_ = v___y_2232_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2234_);
                    v___x_2244_ = lean_box(0);
                    v___y_2194_ = v_name_2230_;
                    v___y_2195_ = v___y_2222_;
                    v___y_2196_ = v___y_2223_;
                    v___y_2197_ = v___y_2224_;
                    v___y_2198_ = v___y_2225_;
                    v___y_2199_ = v___y_2227_;
                    v___y_2200_ = v___y_2228_;
                    v___y_2201_ = v___y_2229_;
                    v_prio_2202_ = v___x_2244_;
                    v___y_2203_ = v___y_2231_;
                    v___y_2204_ = v___y_2232_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                lean_inc_ref(v___y_2248_);
                v___x_2266_ = l_Array_append___redArg(v___y_2248_, v___y_2265_);
                lean_dec_ref(v___y_2265_);
                lean_inc(v___y_2247_);
                lean_inc(v___y_2254_);
                v___x_2267_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2267_, 0, v___y_2254_);
                lean_ctor_set(v___x_2267_, 1, v___y_2247_);
                lean_ctor_set(v___x_2267_, 2, v___x_2266_);
                if lean_obj_tag(v___y_2249_) == 1 {
                    v_val_2268_ = lean_ctor_get(v___y_2249_, 0);
                    lean_inc(v_val_2268_);
                    lean_dec_ref_known(v___y_2249_, 1);
                    v___x_2269_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2270_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2254_, 5);
                    v___x_2271_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2271_, 0, v___y_2254_);
                    lean_ctor_set(v___x_2271_, 1, v___x_2270_);
                    v___x_2272_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2273_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2273_, 0, v___y_2254_);
                    lean_ctor_set(v___x_2273_, 1, v___x_2272_);
                    v___x_2274_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2275_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2275_, 0, v___y_2254_);
                    lean_ctor_set(v___x_2275_, 1, v___x_2274_);
                    v___x_2276_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2277_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2277_, 0, v___y_2254_);
                    lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                    v___x_2278_ = l_Lean_Syntax_node5(
                        v___y_2254_,
                        v___x_2269_,
                        v___x_2271_,
                        v___x_2273_,
                        v___x_2275_,
                        v_val_2268_,
                        v___x_2277_,
                    );
                    v___x_2279_ = l_Array_mkArray1___redArg(v___x_2278_);
                    v___y_1750_ = v___y_2246_;
                    v___y_1751_ = v___y_2247_;
                    v___y_1752_ = v___y_2248_;
                    v___y_1753_ = v___y_2250_;
                    v___y_1754_ = v___y_2251_;
                    v___y_1755_ = v___y_2252_;
                    v___y_1756_ = v___y_2253_;
                    v___y_1757_ = v___y_2255_;
                    v___y_1758_ = v___y_2254_;
                    v___y_1759_ = v___y_2256_;
                    v___y_1760_ = v___y_2257_;
                    v___y_1761_ = v___x_2267_;
                    v___y_1762_ = v___y_2258_;
                    v___y_1763_ = v___y_2260_;
                    v___y_1764_ = v___y_2259_;
                    v___y_1765_ = v___y_2262_;
                    v___y_1766_ = v___y_2261_;
                    v___y_1767_ = v___y_2263_;
                    v___y_1768_ = v___y_2264_;
                    v___y_1769_ = v___x_2279_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___y_2249_);
                    v___x_2280_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1750_ = v___y_2246_;
                    v___y_1751_ = v___y_2247_;
                    v___y_1752_ = v___y_2248_;
                    v___y_1753_ = v___y_2250_;
                    v___y_1754_ = v___y_2251_;
                    v___y_1755_ = v___y_2252_;
                    v___y_1756_ = v___y_2253_;
                    v___y_1757_ = v___y_2255_;
                    v___y_1758_ = v___y_2254_;
                    v___y_1759_ = v___y_2256_;
                    v___y_1760_ = v___y_2257_;
                    v___y_1761_ = v___x_2267_;
                    v___y_1762_ = v___y_2258_;
                    v___y_1763_ = v___y_2260_;
                    v___y_1764_ = v___y_2259_;
                    v___y_1765_ = v___y_2262_;
                    v___y_1766_ = v___y_2261_;
                    v___y_1767_ = v___y_2263_;
                    v___y_1768_ = v___y_2264_;
                    v___y_1769_ = v___x_2280_;
                    state = 3;
                    continue;
                }
            }
            17 => {
                lean_inc_ref_n(v___y_2285_, 2);
                v___x_2301_ = l_Array_append___redArg(v___y_2285_, v___y_2300_);
                lean_dec_ref(v___y_2300_);
                lean_inc_n(v___y_2284_, 3);
                lean_inc_n(v___y_2290_, 7);
                v___x_2302_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2302_, 0, v___y_2290_);
                lean_ctor_set(v___x_2302_, 1, v___y_2284_);
                lean_ctor_set(v___x_2302_, 2, v___x_2301_);
                v___x_2303_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2303_, 0, v___y_2290_);
                lean_ctor_set(v___x_2303_, 1, v___y_2284_);
                lean_ctor_set(v___x_2303_, 2, v___y_2285_);
                lean_inc(v___y_2282_);
                v___x_2304_ = l_Lean_Syntax_node1(v___y_2290_, v___y_2282_, v___x_2303_);
                lean_inc_ref(v___y_2298_);
                v___x_2305_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2305_, 0, v___y_2290_);
                lean_ctor_set(v___x_2305_, 1, v___y_2298_);
                v___x_2306_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2307_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2307_, 0, v___y_2290_);
                lean_ctor_set(v___x_2307_, 1, v___x_2306_);
                lean_inc_ref(v___x_2307_);
                lean_inc(v___y_2289_);
                v___x_2308_ =
                    l_Lean_Syntax_node2(v___y_2290_, v___y_2289_, v___x_2307_, v___y_2286_);
                v___x_2309_ = l_Lean_Syntax_node1(v___y_2290_, v___y_2284_, v___x_2308_);
                if lean_obj_tag(v___y_2294_) == 1 {
                    v_val_2310_ = lean_ctor_get(v___y_2294_, 0);
                    lean_inc(v_val_2310_);
                    lean_dec_ref_known(v___y_2294_, 1);
                    v___x_2311_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2312_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2290_, 5);
                    v___x_2313_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2313_, 0, v___y_2290_);
                    lean_ctor_set(v___x_2313_, 1, v___x_2312_);
                    v___x_2314_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2315_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2315_, 0, v___y_2290_);
                    lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                    v___x_2316_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2317_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2317_, 0, v___y_2290_);
                    lean_ctor_set(v___x_2317_, 1, v___x_2316_);
                    v___x_2318_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2319_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2319_, 0, v___y_2290_);
                    lean_ctor_set(v___x_2319_, 1, v___x_2318_);
                    v___x_2320_ = l_Lean_Syntax_node5(
                        v___y_2290_,
                        v___x_2311_,
                        v___x_2313_,
                        v___x_2315_,
                        v___x_2317_,
                        v_val_2310_,
                        v___x_2319_,
                    );
                    v___x_2321_ = l_Array_mkArray1___redArg(v___x_2320_);
                    v___y_2246_ = v___y_2283_;
                    v___y_2247_ = v___y_2284_;
                    v___y_2248_ = v___y_2285_;
                    v___y_2249_ = v___y_2287_;
                    v___y_2250_ = v___y_2288_;
                    v___y_2251_ = v___x_2307_;
                    v___y_2252_ = v___x_2309_;
                    v___y_2253_ = v___y_2289_;
                    v___y_2254_ = v___y_2290_;
                    v___y_2255_ = v___y_2291_;
                    v___y_2256_ = v___y_2292_;
                    v___y_2257_ = v___x_2305_;
                    v___y_2258_ = v___x_2302_;
                    v___y_2259_ = v___y_2293_;
                    v___y_2260_ = v___x_2304_;
                    v___y_2261_ = v___y_2296_;
                    v___y_2262_ = v___y_2295_;
                    v___y_2263_ = v___y_2297_;
                    v___y_2264_ = v___y_2299_;
                    v___y_2265_ = v___x_2321_;
                    state = 16;
                    continue;
                } else {
                    lean_dec(v___y_2294_);
                    v___x_2322_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2246_ = v___y_2283_;
                    v___y_2247_ = v___y_2284_;
                    v___y_2248_ = v___y_2285_;
                    v___y_2249_ = v___y_2287_;
                    v___y_2250_ = v___y_2288_;
                    v___y_2251_ = v___x_2307_;
                    v___y_2252_ = v___x_2309_;
                    v___y_2253_ = v___y_2289_;
                    v___y_2254_ = v___y_2290_;
                    v___y_2255_ = v___y_2291_;
                    v___y_2256_ = v___y_2292_;
                    v___y_2257_ = v___x_2305_;
                    v___y_2258_ = v___x_2302_;
                    v___y_2259_ = v___y_2293_;
                    v___y_2260_ = v___x_2304_;
                    v___y_2261_ = v___y_2296_;
                    v___y_2262_ = v___y_2295_;
                    v___y_2263_ = v___y_2297_;
                    v___y_2264_ = v___y_2299_;
                    v___y_2265_ = v___x_2322_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                lean_inc_ref(v___y_2327_);
                v___x_2343_ = l_Array_append___redArg(v___y_2327_, v___y_2342_);
                lean_dec_ref(v___y_2342_);
                lean_inc(v___y_2326_);
                lean_inc(v___y_2333_);
                v___x_2344_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2344_, 0, v___y_2333_);
                lean_ctor_set(v___x_2344_, 1, v___y_2326_);
                lean_ctor_set(v___x_2344_, 2, v___x_2343_);
                if lean_obj_tag(v___y_2331_) == 1 {
                    v_val_2345_ = lean_ctor_get(v___y_2331_, 0);
                    lean_inc(v_val_2345_);
                    lean_dec_ref_known(v___y_2331_, 1);
                    v___x_2346_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    lean_inc_ref(v___y_2335_);
                    v___x_2347_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2335_, v___x_2346_);
                    v___x_2348_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    lean_inc_n(v___y_2333_, 4);
                    v___x_2349_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2349_, 0, v___y_2333_);
                    lean_ctor_set(v___x_2349_, 1, v___x_2348_);
                    lean_inc_ref(v___y_2327_);
                    v___x_2350_ = l_Array_append___redArg(v___y_2327_, v_val_2345_);
                    lean_dec(v_val_2345_);
                    lean_inc(v___y_2326_);
                    v___x_2351_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2351_, 0, v___y_2333_);
                    lean_ctor_set(v___x_2351_, 1, v___y_2326_);
                    lean_ctor_set(v___x_2351_, 2, v___x_2350_);
                    v___x_2352_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2353_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2353_, 0, v___y_2333_);
                    lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                    v___x_2354_ = l_Lean_Syntax_node3(
                        v___y_2333_,
                        v___x_2347_,
                        v___x_2349_,
                        v___x_2351_,
                        v___x_2353_,
                    );
                    v___x_2355_ = l_Array_mkArray1___redArg(v___x_2354_);
                    v___y_2282_ = v___y_2324_;
                    v___y_2283_ = v___y_2325_;
                    v___y_2284_ = v___y_2326_;
                    v___y_2285_ = v___y_2327_;
                    v___y_2286_ = v___y_2328_;
                    v___y_2287_ = v___y_2329_;
                    v___y_2288_ = v___y_2330_;
                    v___y_2289_ = v___y_2332_;
                    v___y_2290_ = v___y_2333_;
                    v___y_2291_ = v___y_2334_;
                    v___y_2292_ = v___y_2335_;
                    v___y_2293_ = v___y_2336_;
                    v___y_2294_ = v___y_2338_;
                    v___y_2295_ = v___y_2337_;
                    v___y_2296_ = v___x_2344_;
                    v___y_2297_ = v___y_2340_;
                    v___y_2298_ = v___y_2339_;
                    v___y_2299_ = v___y_2341_;
                    v___y_2300_ = v___x_2355_;
                    state = 17;
                    continue;
                } else {
                    lean_dec(v___y_2331_);
                    v___x_2356_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2282_ = v___y_2324_;
                    v___y_2283_ = v___y_2325_;
                    v___y_2284_ = v___y_2326_;
                    v___y_2285_ = v___y_2327_;
                    v___y_2286_ = v___y_2328_;
                    v___y_2287_ = v___y_2329_;
                    v___y_2288_ = v___y_2330_;
                    v___y_2289_ = v___y_2332_;
                    v___y_2290_ = v___y_2333_;
                    v___y_2291_ = v___y_2334_;
                    v___y_2292_ = v___y_2335_;
                    v___y_2293_ = v___y_2336_;
                    v___y_2294_ = v___y_2338_;
                    v___y_2295_ = v___y_2337_;
                    v___y_2296_ = v___x_2344_;
                    v___y_2297_ = v___y_2340_;
                    v___y_2298_ = v___y_2339_;
                    v___y_2299_ = v___y_2341_;
                    v___y_2300_ = v___x_2356_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                lean_inc(v___y_2361_);
                v___x_2370_ = l_Lean_evalPrec(v___y_2361_, v___y_2368_, v___y_2369_);
                if lean_obj_tag(v___x_2370_) == 0 {
                    v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
                    lean_inc(v_a_2371_);
                    v_a_2372_ = lean_ctor_get(v___x_2370_, 1);
                    lean_inc(v_a_2372_);
                    lean_dec_ref_known(v___x_2370_, 2);
                    v_quotContext_2373_ = lean_ctor_get(v___y_2368_, 1);
                    v_currMacroScope_2374_ = lean_ctor_get(v___y_2368_, 2);
                    v_ref_2375_ = lean_ctor_get(v___y_2368_, 5);
                    v___x_2376_ = lean_unsigned_to_nat(7);
                    v___x_2377_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2376_);
                    v___x_2378_ = lean_unsigned_to_nat(9);
                    v___x_2379_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2378_);
                    lean_dec(v_stx_1648_);
                    v___x_2380_ = lean_nat_add(v_a_2371_, v___y_2358_);
                    lean_dec(v_a_2371_);
                    v___x_2381_ = l_Nat_reprFast(v___x_2380_);
                    v___x_2382_ = lean_box(2);
                    v___x_2383_ = l_Lean_Syntax_mkNumLit(v___x_2381_, v___x_2382_);
                    v___x_2384_ = l_Lean_SourceInfo_fromRef(v_ref_2375_, v___y_2359_);
                    v___x_2385_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                    v___x_2386_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                    v___x_2387_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                    v___x_2388_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                        ),
                        _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                    );
                    if lean_obj_tag(v___y_2364_) == 1 {
                        v_val_2389_ = lean_ctor_get(v___y_2364_, 0);
                        lean_inc(v_val_2389_);
                        lean_dec_ref_known(v___y_2364_, 1);
                        v___x_2390_ = l_Array_mkArray1___redArg(v_val_2389_);
                        v___y_2324_ = v___y_2360_;
                        v___y_2325_ = v_quotContext_2373_;
                        v___y_2326_ = v___x_2387_;
                        v___y_2327_ = v___x_2388_;
                        v___y_2328_ = v___y_2361_;
                        v___y_2329_ = v_prio_2367_;
                        v___y_2330_ = v___x_2379_;
                        v___y_2331_ = v___y_2363_;
                        v___y_2332_ = v___y_2365_;
                        v___y_2333_ = v___x_2384_;
                        v___y_2334_ = v___x_2386_;
                        v___y_2335_ = v___y_2366_;
                        v___y_2336_ = v_currMacroScope_2374_;
                        v___y_2337_ = v___x_2383_;
                        v___y_2338_ = v___y_2362_;
                        v___y_2339_ = v___x_2385_;
                        v___y_2340_ = v_a_2372_;
                        v___y_2341_ = v___x_2377_;
                        v___y_2342_ = v___x_2390_;
                        state = 18;
                        continue;
                    } else {
                        lean_dec(v___y_2364_);
                        v___x_2391_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                        v___y_2324_ = v___y_2360_;
                        v___y_2325_ = v_quotContext_2373_;
                        v___y_2326_ = v___x_2387_;
                        v___y_2327_ = v___x_2388_;
                        v___y_2328_ = v___y_2361_;
                        v___y_2329_ = v_prio_2367_;
                        v___y_2330_ = v___x_2379_;
                        v___y_2331_ = v___y_2363_;
                        v___y_2332_ = v___y_2365_;
                        v___y_2333_ = v___x_2384_;
                        v___y_2334_ = v___x_2386_;
                        v___y_2335_ = v___y_2366_;
                        v___y_2336_ = v_currMacroScope_2374_;
                        v___y_2337_ = v___x_2383_;
                        v___y_2338_ = v___y_2362_;
                        v___y_2339_ = v___x_2385_;
                        v___y_2340_ = v_a_2372_;
                        v___y_2341_ = v___x_2377_;
                        v___y_2342_ = v___x_2391_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_dec(v_prio_2367_);
                    lean_dec(v___y_2364_);
                    lean_dec(v___y_2363_);
                    lean_dec(v___y_2362_);
                    lean_dec(v___y_2361_);
                    lean_dec(v_stx_1648_);
                    v_a_2392_ = lean_ctor_get(v___x_2370_, 0);
                    v_a_2393_ = lean_ctor_get(v___x_2370_, 1);
                    v_isSharedCheck_2400_ = (!lean_is_exclusive(v___x_2370_)) as u8;
                    if v_isSharedCheck_2400_ == 0 {
                        v___x_2395_ = v___x_2370_;
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_2393_);
                        lean_inc(v_a_2392_);
                        lean_dec(v___x_2370_);
                        v___x_2395_ = lean_box(0);
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_2396_ == 0 {
                    v___x_2398_ = v___x_2395_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2392_);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_a_2393_);
                    v___x_2398_ = v_reuseFailAlloc_2399_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2398_;
            }
            22 => {
                v___x_2414_ = lean_unsigned_to_nat(6);
                v___x_2415_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2414_);
                v___x_2416_ = l_Lean_Syntax_isNone(v___x_2415_);
                if v___x_2416_ == 0 {
                    lean_inc(v___x_2415_);
                    v___x_2417_ = l_Lean_Syntax_matchesNull(v___x_2415_, v___y_2402_);
                    if v___x_2417_ == 0 {
                        lean_dec(v___x_2415_);
                        lean_dec(v_name_2411_);
                        lean_dec(v___y_2409_);
                        lean_dec(v___y_2406_);
                        lean_dec(v___y_2405_);
                        lean_dec(v_stx_1648_);
                        v___x_2418_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2413_);
                        return v___x_2418_;
                    } else {
                        v___x_2419_ = l_Lean_Syntax_getArg(v___x_2415_, v___x_1926_);
                        lean_dec(v___x_2415_);
                        v___x_2420_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        lean_inc(v___x_2419_);
                        v___x_2421_ = l_Lean_Syntax_isOfKind(v___x_2419_, v___x_2420_);
                        if v___x_2421_ == 0 {
                            lean_dec(v___x_2419_);
                            lean_dec(v_name_2411_);
                            lean_dec(v___y_2409_);
                            lean_dec(v___y_2406_);
                            lean_dec(v___y_2405_);
                            lean_dec(v_stx_1648_);
                            v___x_2422_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2413_);
                            return v___x_2422_;
                        } else {
                            v_prio_2423_ = l_Lean_Syntax_getArg(v___x_2419_, v___y_2407_);
                            lean_dec(v___x_2419_);
                            v___x_2424_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2424_, 0, v_prio_2423_);
                            v___y_2358_ = v___y_2402_;
                            v___y_2359_ = v___y_2403_;
                            v___y_2360_ = v___y_2404_;
                            v___y_2361_ = v___y_2405_;
                            v___y_2362_ = v_name_2411_;
                            v___y_2363_ = v___y_2406_;
                            v___y_2364_ = v___y_2409_;
                            v___y_2365_ = v___y_2408_;
                            v___y_2366_ = v___y_2410_;
                            v_prio_2367_ = v___x_2424_;
                            v___y_2368_ = v___y_2412_;
                            v___y_2369_ = v___y_2413_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2415_);
                    v___x_2425_ = lean_box(0);
                    v___y_2358_ = v___y_2402_;
                    v___y_2359_ = v___y_2403_;
                    v___y_2360_ = v___y_2404_;
                    v___y_2361_ = v___y_2405_;
                    v___y_2362_ = v_name_2411_;
                    v___y_2363_ = v___y_2406_;
                    v___y_2364_ = v___y_2409_;
                    v___y_2365_ = v___y_2408_;
                    v___y_2366_ = v___y_2410_;
                    v_prio_2367_ = v___x_2425_;
                    v___y_2368_ = v___y_2412_;
                    v___y_2369_ = v___y_2413_;
                    state = 19;
                    continue;
                }
            }
            23 => {
                lean_inc_ref(v___y_2445_);
                v___x_2447_ = l_Array_append___redArg(v___y_2445_, v___y_2446_);
                lean_dec_ref(v___y_2446_);
                lean_inc(v___y_2428_);
                lean_inc(v___y_2432_);
                v___x_2448_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2448_, 0, v___y_2432_);
                lean_ctor_set(v___x_2448_, 1, v___y_2428_);
                lean_ctor_set(v___x_2448_, 2, v___x_2447_);
                if lean_obj_tag(v___y_2442_) == 1 {
                    v_val_2449_ = lean_ctor_get(v___y_2442_, 0);
                    lean_inc(v_val_2449_);
                    lean_dec_ref_known(v___y_2442_, 1);
                    v___x_2450_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2451_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2432_, 5);
                    v___x_2452_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2452_, 0, v___y_2432_);
                    lean_ctor_set(v___x_2452_, 1, v___x_2451_);
                    v___x_2453_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2454_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2454_, 0, v___y_2432_);
                    lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                    v___x_2455_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2456_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2456_, 0, v___y_2432_);
                    lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                    v___x_2457_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2458_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2458_, 0, v___y_2432_);
                    lean_ctor_set(v___x_2458_, 1, v___x_2457_);
                    v___x_2459_ = l_Lean_Syntax_node5(
                        v___y_2432_,
                        v___x_2450_,
                        v___x_2452_,
                        v___x_2454_,
                        v___x_2456_,
                        v_val_2449_,
                        v___x_2458_,
                    );
                    v___x_2460_ = l_Array_mkArray1___redArg(v___x_2459_);
                    v___y_1808_ = v___y_2427_;
                    v___y_1809_ = v___y_2428_;
                    v___y_1810_ = v___y_2429_;
                    v___y_1811_ = v___y_2430_;
                    v___y_1812_ = v___y_2431_;
                    v___y_1813_ = v___y_2432_;
                    v___y_1814_ = v___y_2433_;
                    v___y_1815_ = v___y_2434_;
                    v___y_1816_ = v___x_2448_;
                    v___y_1817_ = v___y_2435_;
                    v___y_1818_ = v___y_2436_;
                    v___y_1819_ = v___y_2437_;
                    v___y_1820_ = v___y_2438_;
                    v___y_1821_ = v___y_2439_;
                    v___y_1822_ = v___y_2441_;
                    v___y_1823_ = v___y_2440_;
                    v___y_1824_ = v___y_2443_;
                    v___y_1825_ = v___y_2444_;
                    v___y_1826_ = v___y_2445_;
                    v___y_1827_ = v___x_2460_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v___y_2442_);
                    v___x_2461_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1808_ = v___y_2427_;
                    v___y_1809_ = v___y_2428_;
                    v___y_1810_ = v___y_2429_;
                    v___y_1811_ = v___y_2430_;
                    v___y_1812_ = v___y_2431_;
                    v___y_1813_ = v___y_2432_;
                    v___y_1814_ = v___y_2433_;
                    v___y_1815_ = v___y_2434_;
                    v___y_1816_ = v___x_2448_;
                    v___y_1817_ = v___y_2435_;
                    v___y_1818_ = v___y_2436_;
                    v___y_1819_ = v___y_2437_;
                    v___y_1820_ = v___y_2438_;
                    v___y_1821_ = v___y_2439_;
                    v___y_1822_ = v___y_2441_;
                    v___y_1823_ = v___y_2440_;
                    v___y_1824_ = v___y_2443_;
                    v___y_1825_ = v___y_2444_;
                    v___y_1826_ = v___y_2445_;
                    v___y_1827_ = v___x_2461_;
                    state = 4;
                    continue;
                }
            }
            24 => {
                lean_inc_ref_n(v___y_2480_, 2);
                v___x_2482_ = l_Array_append___redArg(v___y_2480_, v___y_2481_);
                lean_dec_ref(v___y_2481_);
                lean_inc_n(v___y_2463_, 3);
                lean_inc_n(v___y_2468_, 7);
                v___x_2483_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2483_, 0, v___y_2468_);
                lean_ctor_set(v___x_2483_, 1, v___y_2463_);
                lean_ctor_set(v___x_2483_, 2, v___x_2482_);
                v___x_2484_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2484_, 0, v___y_2468_);
                lean_ctor_set(v___x_2484_, 1, v___y_2463_);
                lean_ctor_set(v___x_2484_, 2, v___y_2480_);
                lean_inc(v___y_2464_);
                v___x_2485_ = l_Lean_Syntax_node1(v___y_2468_, v___y_2464_, v___x_2484_);
                lean_inc_ref(v___y_2477_);
                v___x_2486_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2486_, 0, v___y_2468_);
                lean_ctor_set(v___x_2486_, 1, v___y_2477_);
                v___x_2487_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2488_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2488_, 0, v___y_2468_);
                lean_ctor_set(v___x_2488_, 1, v___x_2487_);
                lean_inc_ref(v___x_2488_);
                lean_inc(v___y_2471_);
                v___x_2489_ =
                    l_Lean_Syntax_node2(v___y_2468_, v___y_2471_, v___x_2488_, v___y_2465_);
                v___x_2490_ = l_Lean_Syntax_node1(v___y_2468_, v___y_2463_, v___x_2489_);
                if lean_obj_tag(v___y_2473_) == 1 {
                    v_val_2491_ = lean_ctor_get(v___y_2473_, 0);
                    lean_inc(v_val_2491_);
                    lean_dec_ref_known(v___y_2473_, 1);
                    v___x_2492_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2493_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2468_, 5);
                    v___x_2494_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2494_, 0, v___y_2468_);
                    lean_ctor_set(v___x_2494_, 1, v___x_2493_);
                    v___x_2495_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2496_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2496_, 0, v___y_2468_);
                    lean_ctor_set(v___x_2496_, 1, v___x_2495_);
                    v___x_2497_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2498_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2498_, 0, v___y_2468_);
                    lean_ctor_set(v___x_2498_, 1, v___x_2497_);
                    v___x_2499_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2500_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2500_, 0, v___y_2468_);
                    lean_ctor_set(v___x_2500_, 1, v___x_2499_);
                    v___x_2501_ = l_Lean_Syntax_node5(
                        v___y_2468_,
                        v___x_2492_,
                        v___x_2494_,
                        v___x_2496_,
                        v___x_2498_,
                        v_val_2491_,
                        v___x_2500_,
                    );
                    v___x_2502_ = l_Array_mkArray1___redArg(v___x_2501_);
                    v___y_2427_ = v___x_2488_;
                    v___y_2428_ = v___y_2463_;
                    v___y_2429_ = v___y_2466_;
                    v___y_2430_ = v___y_2467_;
                    v___y_2431_ = v___x_2485_;
                    v___y_2432_ = v___y_2468_;
                    v___y_2433_ = v___x_2490_;
                    v___y_2434_ = v___x_2486_;
                    v___y_2435_ = v___y_2469_;
                    v___y_2436_ = v___y_2470_;
                    v___y_2437_ = v___y_2471_;
                    v___y_2438_ = v___y_2472_;
                    v___y_2439_ = v___y_2474_;
                    v___y_2440_ = v___y_2476_;
                    v___y_2441_ = v___y_2475_;
                    v___y_2442_ = v___y_2479_;
                    v___y_2443_ = v___y_2478_;
                    v___y_2444_ = v___x_2483_;
                    v___y_2445_ = v___y_2480_;
                    v___y_2446_ = v___x_2502_;
                    state = 23;
                    continue;
                } else {
                    lean_dec(v___y_2473_);
                    v___x_2503_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2427_ = v___x_2488_;
                    v___y_2428_ = v___y_2463_;
                    v___y_2429_ = v___y_2466_;
                    v___y_2430_ = v___y_2467_;
                    v___y_2431_ = v___x_2485_;
                    v___y_2432_ = v___y_2468_;
                    v___y_2433_ = v___x_2490_;
                    v___y_2434_ = v___x_2486_;
                    v___y_2435_ = v___y_2469_;
                    v___y_2436_ = v___y_2470_;
                    v___y_2437_ = v___y_2471_;
                    v___y_2438_ = v___y_2472_;
                    v___y_2439_ = v___y_2474_;
                    v___y_2440_ = v___y_2476_;
                    v___y_2441_ = v___y_2475_;
                    v___y_2442_ = v___y_2479_;
                    v___y_2443_ = v___y_2478_;
                    v___y_2444_ = v___x_2483_;
                    v___y_2445_ = v___y_2480_;
                    v___y_2446_ = v___x_2503_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                lean_inc_ref(v___y_2522_);
                v___x_2524_ = l_Array_append___redArg(v___y_2522_, v___y_2523_);
                lean_dec_ref(v___y_2523_);
                lean_inc(v___y_2505_);
                lean_inc(v___y_2510_);
                v___x_2525_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2525_, 0, v___y_2510_);
                lean_ctor_set(v___x_2525_, 1, v___y_2505_);
                lean_ctor_set(v___x_2525_, 2, v___x_2524_);
                if lean_obj_tag(v___y_2511_) == 1 {
                    v_val_2526_ = lean_ctor_get(v___y_2511_, 0);
                    lean_inc(v_val_2526_);
                    lean_dec_ref_known(v___y_2511_, 1);
                    v___x_2527_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    lean_inc_ref(v___y_2512_);
                    v___x_2528_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2512_, v___x_2527_);
                    v___x_2529_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    lean_inc_n(v___y_2510_, 4);
                    v___x_2530_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2530_, 0, v___y_2510_);
                    lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                    lean_inc_ref(v___y_2522_);
                    v___x_2531_ = l_Array_append___redArg(v___y_2522_, v_val_2526_);
                    lean_dec(v_val_2526_);
                    lean_inc(v___y_2505_);
                    v___x_2532_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2532_, 0, v___y_2510_);
                    lean_ctor_set(v___x_2532_, 1, v___y_2505_);
                    lean_ctor_set(v___x_2532_, 2, v___x_2531_);
                    v___x_2533_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2534_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2534_, 0, v___y_2510_);
                    lean_ctor_set(v___x_2534_, 1, v___x_2533_);
                    v___x_2535_ = l_Lean_Syntax_node3(
                        v___y_2510_,
                        v___x_2528_,
                        v___x_2530_,
                        v___x_2532_,
                        v___x_2534_,
                    );
                    v___x_2536_ = l_Array_mkArray1___redArg(v___x_2535_);
                    v___y_2463_ = v___y_2505_;
                    v___y_2464_ = v___y_2506_;
                    v___y_2465_ = v___y_2507_;
                    v___y_2466_ = v___y_2508_;
                    v___y_2467_ = v___y_2509_;
                    v___y_2468_ = v___y_2510_;
                    v___y_2469_ = v___y_2512_;
                    v___y_2470_ = v___x_2525_;
                    v___y_2471_ = v___y_2513_;
                    v___y_2472_ = v___y_2514_;
                    v___y_2473_ = v___y_2515_;
                    v___y_2474_ = v___y_2516_;
                    v___y_2475_ = v___y_2519_;
                    v___y_2476_ = v___y_2518_;
                    v___y_2477_ = v___y_2517_;
                    v___y_2478_ = v___y_2521_;
                    v___y_2479_ = v___y_2520_;
                    v___y_2480_ = v___y_2522_;
                    v___y_2481_ = v___x_2536_;
                    state = 24;
                    continue;
                } else {
                    lean_dec(v___y_2511_);
                    v___x_2537_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2463_ = v___y_2505_;
                    v___y_2464_ = v___y_2506_;
                    v___y_2465_ = v___y_2507_;
                    v___y_2466_ = v___y_2508_;
                    v___y_2467_ = v___y_2509_;
                    v___y_2468_ = v___y_2510_;
                    v___y_2469_ = v___y_2512_;
                    v___y_2470_ = v___x_2525_;
                    v___y_2471_ = v___y_2513_;
                    v___y_2472_ = v___y_2514_;
                    v___y_2473_ = v___y_2515_;
                    v___y_2474_ = v___y_2516_;
                    v___y_2475_ = v___y_2519_;
                    v___y_2476_ = v___y_2518_;
                    v___y_2477_ = v___y_2517_;
                    v___y_2478_ = v___y_2521_;
                    v___y_2479_ = v___y_2520_;
                    v___y_2480_ = v___y_2522_;
                    v___y_2481_ = v___x_2537_;
                    state = 24;
                    continue;
                }
            }
            26 => {
                lean_inc(v___y_2543_);
                v___x_2551_ = l_Lean_evalPrec(v___y_2543_, v___y_2549_, v___y_2550_);
                if lean_obj_tag(v___x_2551_) == 0 {
                    v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
                    lean_inc(v_a_2552_);
                    v_a_2553_ = lean_ctor_get(v___x_2551_, 1);
                    lean_inc(v_a_2553_);
                    lean_dec_ref_known(v___x_2551_, 2);
                    v_quotContext_2554_ = lean_ctor_get(v___y_2549_, 1);
                    v_currMacroScope_2555_ = lean_ctor_get(v___y_2549_, 2);
                    v_ref_2556_ = lean_ctor_get(v___y_2549_, 5);
                    v___x_2557_ = lean_unsigned_to_nat(7);
                    v___x_2558_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2557_);
                    v___x_2559_ = lean_unsigned_to_nat(9);
                    v___x_2560_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2559_);
                    lean_dec(v_stx_1648_);
                    v___x_2561_ = lean_nat_add(v_a_2552_, v___y_2540_);
                    lean_dec(v_a_2552_);
                    v___x_2562_ = l_Nat_reprFast(v___x_2561_);
                    v___x_2563_ = lean_box(2);
                    v___x_2564_ = l_Lean_Syntax_mkNumLit(v___x_2562_, v___x_2563_);
                    v___x_2565_ = l_Lean_SourceInfo_fromRef(v_ref_2556_, v___y_2544_);
                    v___x_2566_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                    v___x_2567_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                    v___x_2568_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                    v___x_2569_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                        ),
                        _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                    );
                    if lean_obj_tag(v___y_2546_) == 1 {
                        v_val_2570_ = lean_ctor_get(v___y_2546_, 0);
                        lean_inc(v_val_2570_);
                        lean_dec_ref_known(v___y_2546_, 1);
                        v___x_2571_ = l_Array_mkArray1___redArg(v_val_2570_);
                        v___y_2505_ = v___x_2568_;
                        v___y_2506_ = v___y_2542_;
                        v___y_2507_ = v___y_2543_;
                        v___y_2508_ = v___x_2560_;
                        v___y_2509_ = v_a_2553_;
                        v___y_2510_ = v___x_2565_;
                        v___y_2511_ = v___y_2545_;
                        v___y_2512_ = v___y_2547_;
                        v___y_2513_ = v___y_2539_;
                        v___y_2514_ = v_quotContext_2554_;
                        v___y_2515_ = v___y_2541_;
                        v___y_2516_ = v_currMacroScope_2555_;
                        v___y_2517_ = v___x_2566_;
                        v___y_2518_ = v___x_2558_;
                        v___y_2519_ = v___x_2564_;
                        v___y_2520_ = v_prio_2548_;
                        v___y_2521_ = v___x_2567_;
                        v___y_2522_ = v___x_2569_;
                        v___y_2523_ = v___x_2571_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v___y_2546_);
                        v___x_2572_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                        v___y_2505_ = v___x_2568_;
                        v___y_2506_ = v___y_2542_;
                        v___y_2507_ = v___y_2543_;
                        v___y_2508_ = v___x_2560_;
                        v___y_2509_ = v_a_2553_;
                        v___y_2510_ = v___x_2565_;
                        v___y_2511_ = v___y_2545_;
                        v___y_2512_ = v___y_2547_;
                        v___y_2513_ = v___y_2539_;
                        v___y_2514_ = v_quotContext_2554_;
                        v___y_2515_ = v___y_2541_;
                        v___y_2516_ = v_currMacroScope_2555_;
                        v___y_2517_ = v___x_2566_;
                        v___y_2518_ = v___x_2558_;
                        v___y_2519_ = v___x_2564_;
                        v___y_2520_ = v_prio_2548_;
                        v___y_2521_ = v___x_2567_;
                        v___y_2522_ = v___x_2569_;
                        v___y_2523_ = v___x_2572_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_dec(v_prio_2548_);
                    lean_dec(v___y_2546_);
                    lean_dec(v___y_2545_);
                    lean_dec(v___y_2543_);
                    lean_dec(v___y_2541_);
                    lean_dec(v_stx_1648_);
                    v_a_2573_ = lean_ctor_get(v___x_2551_, 0);
                    v_a_2574_ = lean_ctor_get(v___x_2551_, 1);
                    v_isSharedCheck_2581_ = (!lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v___x_2576_ = v___x_2551_;
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_2574_);
                        lean_inc(v_a_2573_);
                        lean_dec(v___x_2551_);
                        v___x_2576_ = lean_box(0);
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2577_ == 0 {
                    v___x_2579_ = v___x_2576_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2573_);
                    lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_a_2574_);
                    v___x_2579_ = v_reuseFailAlloc_2580_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2579_;
            }
            29 => {
                v___x_2595_ = lean_unsigned_to_nat(6);
                v___x_2596_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2595_);
                v___x_2597_ = l_Lean_Syntax_isNone(v___x_2596_);
                if v___x_2597_ == 0 {
                    lean_inc(v___x_2596_);
                    v___x_2598_ = l_Lean_Syntax_matchesNull(v___x_2596_, v___y_2583_);
                    if v___x_2598_ == 0 {
                        lean_dec(v___x_2596_);
                        lean_dec(v_name_2592_);
                        lean_dec(v___y_2590_);
                        lean_dec(v___y_2588_);
                        lean_dec(v___y_2586_);
                        lean_dec(v_stx_1648_);
                        v___x_2599_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2594_);
                        return v___x_2599_;
                    } else {
                        v___x_2600_ = l_Lean_Syntax_getArg(v___x_2596_, v___x_1926_);
                        lean_dec(v___x_2596_);
                        v___x_2601_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        lean_inc(v___x_2600_);
                        v___x_2602_ = l_Lean_Syntax_isOfKind(v___x_2600_, v___x_2601_);
                        if v___x_2602_ == 0 {
                            lean_dec(v___x_2600_);
                            lean_dec(v_name_2592_);
                            lean_dec(v___y_2590_);
                            lean_dec(v___y_2588_);
                            lean_dec(v___y_2586_);
                            lean_dec(v_stx_1648_);
                            v___x_2603_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2594_);
                            return v___x_2603_;
                        } else {
                            v_prio_2604_ = l_Lean_Syntax_getArg(v___x_2600_, v___y_2589_);
                            lean_dec(v___x_2600_);
                            v___x_2605_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2605_, 0, v_prio_2604_);
                            v___y_2539_ = v___y_2584_;
                            v___y_2540_ = v___y_2583_;
                            v___y_2541_ = v_name_2592_;
                            v___y_2542_ = v___y_2585_;
                            v___y_2543_ = v___y_2586_;
                            v___y_2544_ = v___y_2587_;
                            v___y_2545_ = v___y_2588_;
                            v___y_2546_ = v___y_2590_;
                            v___y_2547_ = v___y_2591_;
                            v_prio_2548_ = v___x_2605_;
                            v___y_2549_ = v___y_2593_;
                            v___y_2550_ = v___y_2594_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2596_);
                    v___x_2606_ = lean_box(0);
                    v___y_2539_ = v___y_2584_;
                    v___y_2540_ = v___y_2583_;
                    v___y_2541_ = v_name_2592_;
                    v___y_2542_ = v___y_2585_;
                    v___y_2543_ = v___y_2586_;
                    v___y_2544_ = v___y_2587_;
                    v___y_2545_ = v___y_2588_;
                    v___y_2546_ = v___y_2590_;
                    v___y_2547_ = v___y_2591_;
                    v_prio_2548_ = v___x_2606_;
                    v___y_2549_ = v___y_2593_;
                    v___y_2550_ = v___y_2594_;
                    state = 26;
                    continue;
                }
            }
            30 => {
                lean_inc_ref(v___y_2621_);
                v___x_2628_ = l_Array_append___redArg(v___y_2621_, v___y_2627_);
                lean_dec_ref(v___y_2627_);
                lean_inc(v___y_2618_);
                lean_inc(v___y_2624_);
                v___x_2629_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2629_, 0, v___y_2624_);
                lean_ctor_set(v___x_2629_, 1, v___y_2618_);
                lean_ctor_set(v___x_2629_, 2, v___x_2628_);
                if lean_obj_tag(v___y_2612_) == 1 {
                    v_val_2630_ = lean_ctor_get(v___y_2612_, 0);
                    lean_inc(v_val_2630_);
                    lean_dec_ref_known(v___y_2612_, 1);
                    v___x_2631_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                    v___x_2632_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2624_, 5);
                    v___x_2633_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2633_, 0, v___y_2624_);
                    lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                    v___x_2634_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__21;
                    v___x_2635_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2635_, 0, v___y_2624_);
                    lean_ctor_set(v___x_2635_, 1, v___x_2634_);
                    v___x_2636_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2637_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2637_, 0, v___y_2624_);
                    lean_ctor_set(v___x_2637_, 1, v___x_2636_);
                    v___x_2638_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2639_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2639_, 0, v___y_2624_);
                    lean_ctor_set(v___x_2639_, 1, v___x_2638_);
                    v___x_2640_ = l_Lean_Syntax_node5(
                        v___y_2624_,
                        v___x_2631_,
                        v___x_2633_,
                        v___x_2635_,
                        v___x_2637_,
                        v_val_2630_,
                        v___x_2639_,
                    );
                    v___x_2641_ = l_Array_mkArray1___redArg(v___x_2640_);
                    v___y_1866_ = v___y_2608_;
                    v___y_1867_ = v___y_2609_;
                    v___y_1868_ = v___y_2610_;
                    v___y_1869_ = v___y_2611_;
                    v___y_1870_ = v___x_2629_;
                    v___y_1871_ = v___y_2613_;
                    v___y_1872_ = v___y_2614_;
                    v___y_1873_ = v___y_2615_;
                    v___y_1874_ = v___y_2616_;
                    v___y_1875_ = v___y_2617_;
                    v___y_1876_ = v___y_2618_;
                    v___y_1877_ = v___y_2619_;
                    v___y_1878_ = v___y_2620_;
                    v___y_1879_ = v___y_2621_;
                    v___y_1880_ = v___y_2622_;
                    v___y_1881_ = v___y_2623_;
                    v___y_1882_ = v___y_2624_;
                    v___y_1883_ = v___y_2626_;
                    v___y_1884_ = v___y_2625_;
                    v___y_1885_ = v___x_2641_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___y_2612_);
                    v___x_2642_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_1866_ = v___y_2608_;
                    v___y_1867_ = v___y_2609_;
                    v___y_1868_ = v___y_2610_;
                    v___y_1869_ = v___y_2611_;
                    v___y_1870_ = v___x_2629_;
                    v___y_1871_ = v___y_2613_;
                    v___y_1872_ = v___y_2614_;
                    v___y_1873_ = v___y_2615_;
                    v___y_1874_ = v___y_2616_;
                    v___y_1875_ = v___y_2617_;
                    v___y_1876_ = v___y_2618_;
                    v___y_1877_ = v___y_2619_;
                    v___y_1878_ = v___y_2620_;
                    v___y_1879_ = v___y_2621_;
                    v___y_1880_ = v___y_2622_;
                    v___y_1881_ = v___y_2623_;
                    v___y_1882_ = v___y_2624_;
                    v___y_1883_ = v___y_2626_;
                    v___y_1884_ = v___y_2625_;
                    v___y_1885_ = v___x_2642_;
                    state = 5;
                    continue;
                }
            }
            31 => {
                lean_inc_ref_n(v___y_2658_, 2);
                v___x_2663_ = l_Array_append___redArg(v___y_2658_, v___y_2662_);
                lean_dec_ref(v___y_2662_);
                lean_inc_n(v___y_2655_, 3);
                lean_inc_n(v___y_2660_, 7);
                v___x_2664_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2664_, 0, v___y_2660_);
                lean_ctor_set(v___x_2664_, 1, v___y_2655_);
                lean_ctor_set(v___x_2664_, 2, v___x_2663_);
                v___x_2665_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2665_, 0, v___y_2660_);
                lean_ctor_set(v___x_2665_, 1, v___y_2655_);
                lean_ctor_set(v___x_2665_, 2, v___y_2658_);
                lean_inc(v___y_2644_);
                v___x_2666_ = l_Lean_Syntax_node1(v___y_2660_, v___y_2644_, v___x_2665_);
                lean_inc_ref(v___y_2649_);
                v___x_2667_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2667_, 0, v___y_2660_);
                lean_ctor_set(v___x_2667_, 1, v___y_2649_);
                v___x_2668_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__25;
                v___x_2669_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2669_, 0, v___y_2660_);
                lean_ctor_set(v___x_2669_, 1, v___x_2668_);
                lean_inc_ref(v___x_2669_);
                lean_inc(v___y_2653_);
                v___x_2670_ =
                    l_Lean_Syntax_node2(v___y_2660_, v___y_2653_, v___x_2669_, v___y_2646_);
                v___x_2671_ = l_Lean_Syntax_node1(v___y_2660_, v___y_2655_, v___x_2670_);
                if lean_obj_tag(v___y_2656_) == 1 {
                    v_val_2672_ = lean_ctor_get(v___y_2656_, 0);
                    lean_inc(v_val_2672_);
                    lean_dec_ref_known(v___y_2656_, 1);
                    v___x_2673_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                    v___x_2674_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__20;
                    lean_inc_n(v___y_2660_, 5);
                    v___x_2675_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2675_, 0, v___y_2660_);
                    lean_ctor_set(v___x_2675_, 1, v___x_2674_);
                    v___x_2676_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__28;
                    v___x_2677_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2677_, 0, v___y_2660_);
                    lean_ctor_set(v___x_2677_, 1, v___x_2676_);
                    v___x_2678_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__22;
                    v___x_2679_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2679_, 0, v___y_2660_);
                    lean_ctor_set(v___x_2679_, 1, v___x_2678_);
                    v___x_2680_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__23;
                    v___x_2681_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2681_, 0, v___y_2660_);
                    lean_ctor_set(v___x_2681_, 1, v___x_2680_);
                    v___x_2682_ = l_Lean_Syntax_node5(
                        v___y_2660_,
                        v___x_2673_,
                        v___x_2675_,
                        v___x_2677_,
                        v___x_2679_,
                        v_val_2672_,
                        v___x_2681_,
                    );
                    v___x_2683_ = l_Array_mkArray1___redArg(v___x_2682_);
                    v___y_2608_ = v___x_2666_;
                    v___y_2609_ = v___x_2669_;
                    v___y_2610_ = v___y_2645_;
                    v___y_2611_ = v___y_2647_;
                    v___y_2612_ = v___y_2648_;
                    v___y_2613_ = v___y_2650_;
                    v___y_2614_ = v___y_2651_;
                    v___y_2615_ = v___y_2652_;
                    v___y_2616_ = v___y_2653_;
                    v___y_2617_ = v___y_2654_;
                    v___y_2618_ = v___y_2655_;
                    v___y_2619_ = v___x_2671_;
                    v___y_2620_ = v___y_2657_;
                    v___y_2621_ = v___y_2658_;
                    v___y_2622_ = v___y_2659_;
                    v___y_2623_ = v___x_2667_;
                    v___y_2624_ = v___y_2660_;
                    v___y_2625_ = v___y_2661_;
                    v___y_2626_ = v___x_2664_;
                    v___y_2627_ = v___x_2683_;
                    state = 30;
                    continue;
                } else {
                    lean_dec(v___y_2656_);
                    v___x_2684_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2608_ = v___x_2666_;
                    v___y_2609_ = v___x_2669_;
                    v___y_2610_ = v___y_2645_;
                    v___y_2611_ = v___y_2647_;
                    v___y_2612_ = v___y_2648_;
                    v___y_2613_ = v___y_2650_;
                    v___y_2614_ = v___y_2651_;
                    v___y_2615_ = v___y_2652_;
                    v___y_2616_ = v___y_2653_;
                    v___y_2617_ = v___y_2654_;
                    v___y_2618_ = v___y_2655_;
                    v___y_2619_ = v___x_2671_;
                    v___y_2620_ = v___y_2657_;
                    v___y_2621_ = v___y_2658_;
                    v___y_2622_ = v___y_2659_;
                    v___y_2623_ = v___x_2667_;
                    v___y_2624_ = v___y_2660_;
                    v___y_2625_ = v___y_2661_;
                    v___y_2626_ = v___x_2664_;
                    v___y_2627_ = v___x_2684_;
                    state = 30;
                    continue;
                }
            }
            32 => {
                lean_inc_ref(v___y_2700_);
                v___x_2705_ = l_Array_append___redArg(v___y_2700_, v___y_2704_);
                lean_dec_ref(v___y_2704_);
                lean_inc(v___y_2697_);
                lean_inc(v___y_2702_);
                v___x_2706_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2706_, 0, v___y_2702_);
                lean_ctor_set(v___x_2706_, 1, v___y_2697_);
                lean_ctor_set(v___x_2706_, 2, v___x_2705_);
                if lean_obj_tag(v___y_2694_) == 1 {
                    v_val_2707_ = lean_ctor_get(v___y_2694_, 0);
                    lean_inc(v_val_2707_);
                    lean_dec_ref_known(v___y_2694_, 1);
                    v___x_2708_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__29;
                    lean_inc_ref(v___y_2696_);
                    v___x_2709_ =
                        l_Lean_Name_mkStr4(v___x_1651_, v___x_1652_, v___y_2696_, v___x_2708_);
                    v___x_2710_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__30;
                    lean_inc_n(v___y_2702_, 4);
                    v___x_2711_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2711_, 0, v___y_2702_);
                    lean_ctor_set(v___x_2711_, 1, v___x_2710_);
                    lean_inc_ref(v___y_2700_);
                    v___x_2712_ = l_Array_append___redArg(v___y_2700_, v_val_2707_);
                    lean_dec(v_val_2707_);
                    lean_inc(v___y_2697_);
                    v___x_2713_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2713_, 0, v___y_2702_);
                    lean_ctor_set(v___x_2713_, 1, v___y_2697_);
                    lean_ctor_set(v___x_2713_, 2, v___x_2712_);
                    v___x_2714_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__31;
                    v___x_2715_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2715_, 0, v___y_2702_);
                    lean_ctor_set(v___x_2715_, 1, v___x_2714_);
                    v___x_2716_ = l_Lean_Syntax_node3(
                        v___y_2702_,
                        v___x_2709_,
                        v___x_2711_,
                        v___x_2713_,
                        v___x_2715_,
                    );
                    v___x_2717_ = l_Array_mkArray1___redArg(v___x_2716_);
                    v___y_2644_ = v___y_2686_;
                    v___y_2645_ = v___y_2687_;
                    v___y_2646_ = v___y_2688_;
                    v___y_2647_ = v___y_2689_;
                    v___y_2648_ = v___y_2690_;
                    v___y_2649_ = v___y_2691_;
                    v___y_2650_ = v___y_2692_;
                    v___y_2651_ = v___y_2693_;
                    v___y_2652_ = v___x_2706_;
                    v___y_2653_ = v___y_2695_;
                    v___y_2654_ = v___y_2696_;
                    v___y_2655_ = v___y_2697_;
                    v___y_2656_ = v___y_2699_;
                    v___y_2657_ = v___y_2698_;
                    v___y_2658_ = v___y_2700_;
                    v___y_2659_ = v___y_2701_;
                    v___y_2660_ = v___y_2702_;
                    v___y_2661_ = v___y_2703_;
                    v___y_2662_ = v___x_2717_;
                    state = 31;
                    continue;
                } else {
                    lean_dec(v___y_2694_);
                    v___x_2718_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                    v___y_2644_ = v___y_2686_;
                    v___y_2645_ = v___y_2687_;
                    v___y_2646_ = v___y_2688_;
                    v___y_2647_ = v___y_2689_;
                    v___y_2648_ = v___y_2690_;
                    v___y_2649_ = v___y_2691_;
                    v___y_2650_ = v___y_2692_;
                    v___y_2651_ = v___y_2693_;
                    v___y_2652_ = v___x_2706_;
                    v___y_2653_ = v___y_2695_;
                    v___y_2654_ = v___y_2696_;
                    v___y_2655_ = v___y_2697_;
                    v___y_2656_ = v___y_2699_;
                    v___y_2657_ = v___y_2698_;
                    v___y_2658_ = v___y_2700_;
                    v___y_2659_ = v___y_2701_;
                    v___y_2660_ = v___y_2702_;
                    v___y_2661_ = v___y_2703_;
                    v___y_2662_ = v___x_2718_;
                    state = 31;
                    continue;
                }
            }
            33 => {
                lean_inc(v___y_2723_);
                v___x_2731_ = l_Lean_evalPrec(v___y_2723_, v___y_2729_, v___y_2730_);
                if lean_obj_tag(v___x_2731_) == 0 {
                    v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
                    lean_inc(v_a_2732_);
                    v_a_2733_ = lean_ctor_get(v___x_2731_, 1);
                    lean_inc(v_a_2733_);
                    lean_dec_ref_known(v___x_2731_, 2);
                    v_quotContext_2734_ = lean_ctor_get(v___y_2729_, 1);
                    v_currMacroScope_2735_ = lean_ctor_get(v___y_2729_, 2);
                    v_ref_2736_ = lean_ctor_get(v___y_2729_, 5);
                    v___x_2737_ = lean_unsigned_to_nat(7);
                    v___x_2738_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2737_);
                    v___x_2739_ = lean_unsigned_to_nat(9);
                    v___x_2740_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2739_);
                    lean_dec(v_stx_1648_);
                    v___x_2741_ = lean_nat_add(v_a_2732_, v___y_2721_);
                    lean_dec(v_a_2732_);
                    v___x_2742_ = l_Nat_reprFast(v___x_2741_);
                    v___x_2743_ = lean_box(2);
                    v___x_2744_ = l_Lean_Syntax_mkNumLit(v___x_2742_, v___x_2743_);
                    v___x_2745_ = 0;
                    v___x_2746_ = l_Lean_SourceInfo_fromRef(v_ref_2736_, v___x_2745_);
                    v___x_2747_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__32;
                    v___x_2748_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__33;
                    v___x_2749_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__35;
                    v___x_2750_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__36_once
                        ),
                        _init_l_Lean_Elab_Command_expandMixfix___lam__0___closed__36,
                    );
                    if lean_obj_tag(v___y_2725_) == 1 {
                        v_val_2751_ = lean_ctor_get(v___y_2725_, 0);
                        lean_inc(v_val_2751_);
                        lean_dec_ref_known(v___y_2725_, 1);
                        v___x_2752_ = l_Array_mkArray1___redArg(v_val_2751_);
                        v___y_2686_ = v___y_2722_;
                        v___y_2687_ = v___x_2738_;
                        v___y_2688_ = v___y_2723_;
                        v___y_2689_ = v___x_2740_;
                        v___y_2690_ = v_prio_2728_;
                        v___y_2691_ = v___x_2747_;
                        v___y_2692_ = v___x_2748_;
                        v___y_2693_ = v_a_2733_;
                        v___y_2694_ = v___y_2724_;
                        v___y_2695_ = v___y_2726_;
                        v___y_2696_ = v___y_2727_;
                        v___y_2697_ = v___x_2749_;
                        v___y_2698_ = v_currMacroScope_2735_;
                        v___y_2699_ = v___y_2720_;
                        v___y_2700_ = v___x_2750_;
                        v___y_2701_ = v___x_2744_;
                        v___y_2702_ = v___x_2746_;
                        v___y_2703_ = v_quotContext_2734_;
                        v___y_2704_ = v___x_2752_;
                        state = 32;
                        continue;
                    } else {
                        lean_dec(v___y_2725_);
                        v___x_2753_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__24;
                        v___y_2686_ = v___y_2722_;
                        v___y_2687_ = v___x_2738_;
                        v___y_2688_ = v___y_2723_;
                        v___y_2689_ = v___x_2740_;
                        v___y_2690_ = v_prio_2728_;
                        v___y_2691_ = v___x_2747_;
                        v___y_2692_ = v___x_2748_;
                        v___y_2693_ = v_a_2733_;
                        v___y_2694_ = v___y_2724_;
                        v___y_2695_ = v___y_2726_;
                        v___y_2696_ = v___y_2727_;
                        v___y_2697_ = v___x_2749_;
                        v___y_2698_ = v_currMacroScope_2735_;
                        v___y_2699_ = v___y_2720_;
                        v___y_2700_ = v___x_2750_;
                        v___y_2701_ = v___x_2744_;
                        v___y_2702_ = v___x_2746_;
                        v___y_2703_ = v_quotContext_2734_;
                        v___y_2704_ = v___x_2753_;
                        state = 32;
                        continue;
                    }
                } else {
                    lean_dec(v_prio_2728_);
                    lean_dec(v___y_2725_);
                    lean_dec(v___y_2724_);
                    lean_dec(v___y_2723_);
                    lean_dec(v___y_2720_);
                    lean_dec(v_stx_1648_);
                    v_a_2754_ = lean_ctor_get(v___x_2731_, 0);
                    v_a_2755_ = lean_ctor_get(v___x_2731_, 1);
                    v_isSharedCheck_2762_ = (!lean_is_exclusive(v___x_2731_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2757_ = v___x_2731_;
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_a_2755_);
                        lean_inc(v_a_2754_);
                        lean_dec(v___x_2731_);
                        v___x_2757_ = lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 34;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_2758_ == 0 {
                    v___x_2760_ = v___x_2757_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2760_;
            }
            36 => {
                v___x_2775_ = lean_unsigned_to_nat(6);
                v___x_2776_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2775_);
                v___x_2777_ = l_Lean_Syntax_isNone(v___x_2776_);
                if v___x_2777_ == 0 {
                    lean_inc(v___x_2776_);
                    v___x_2778_ = l_Lean_Syntax_matchesNull(v___x_2776_, v___y_2764_);
                    if v___x_2778_ == 0 {
                        lean_dec(v___x_2776_);
                        lean_dec(v_name_2772_);
                        lean_dec(v___y_2770_);
                        lean_dec(v___y_2767_);
                        lean_dec(v___y_2766_);
                        lean_dec(v_stx_1648_);
                        v___x_2779_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2774_);
                        return v___x_2779_;
                    } else {
                        v___x_2780_ = l_Lean_Syntax_getArg(v___x_2776_, v___x_1926_);
                        lean_dec(v___x_2776_);
                        v___x_2781_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__19;
                        lean_inc(v___x_2780_);
                        v___x_2782_ = l_Lean_Syntax_isOfKind(v___x_2780_, v___x_2781_);
                        if v___x_2782_ == 0 {
                            lean_dec(v___x_2780_);
                            lean_dec(v_name_2772_);
                            lean_dec(v___y_2770_);
                            lean_dec(v___y_2767_);
                            lean_dec(v___y_2766_);
                            lean_dec(v_stx_1648_);
                            v___x_2783_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2774_);
                            return v___x_2783_;
                        } else {
                            v_prio_2784_ = l_Lean_Syntax_getArg(v___x_2780_, v___y_2768_);
                            lean_dec(v___x_2780_);
                            v___x_2785_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2785_, 0, v_prio_2784_);
                            v___y_2720_ = v_name_2772_;
                            v___y_2721_ = v___y_2764_;
                            v___y_2722_ = v___y_2765_;
                            v___y_2723_ = v___y_2766_;
                            v___y_2724_ = v___y_2767_;
                            v___y_2725_ = v___y_2770_;
                            v___y_2726_ = v___y_2769_;
                            v___y_2727_ = v___y_2771_;
                            v_prio_2728_ = v___x_2785_;
                            v___y_2729_ = v___y_2773_;
                            v___y_2730_ = v___y_2774_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2776_);
                    v___x_2786_ = lean_box(0);
                    v___y_2720_ = v_name_2772_;
                    v___y_2721_ = v___y_2764_;
                    v___y_2722_ = v___y_2765_;
                    v___y_2723_ = v___y_2766_;
                    v___y_2724_ = v___y_2767_;
                    v___y_2725_ = v___y_2770_;
                    v___y_2726_ = v___y_2769_;
                    v___y_2727_ = v___y_2771_;
                    v_prio_2728_ = v___x_2786_;
                    v___y_2729_ = v___y_2773_;
                    v___y_2730_ = v___y_2774_;
                    state = 33;
                    continue;
                }
            }
            37 => {
                v___x_2793_ = lean_unsigned_to_nat(2);
                v___x_2794_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2793_);
                v___x_2795_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__37;
                v___x_2796_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__39;
                lean_inc(v___x_2794_);
                v___x_2797_ = l_Lean_Syntax_isOfKind(v___x_2794_, v___x_2796_);
                if v___x_2797_ == 0 {
                    lean_dec(v___x_2794_);
                    lean_dec(v_attrs_x3f_2790_);
                    lean_dec(v___y_2789_);
                    lean_dec(v_stx_1648_);
                    v___x_2798_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                    return v___x_2798_;
                } else {
                    v___x_2799_ = l_Lean_Syntax_getArg(v___x_2794_, v___x_1926_);
                    lean_dec(v___x_2794_);
                    v___x_2800_ = l_Lean_Syntax_matchesNull(v___x_2799_, v___x_1926_);
                    if v___x_2800_ == 0 {
                        lean_dec(v_attrs_x3f_2790_);
                        lean_dec(v___y_2789_);
                        lean_dec(v_stx_1648_);
                        v___x_2801_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                        return v___x_2801_;
                    } else {
                        v___x_2802_ = lean_unsigned_to_nat(3);
                        v___x_2803_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2802_);
                        v___x_2804_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__41;
                        lean_inc(v___x_2803_);
                        v___x_2805_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2804_);
                        if v___x_2805_ == 0 {
                            v___x_2806_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__43;
                            lean_inc(v___x_2803_);
                            v___x_2807_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2806_);
                            if v___x_2807_ == 0 {
                                v___x_2808_ =
                                    l_Lean_Elab_Command_expandMixfix___lam__0___closed__45;
                                lean_inc(v___x_2803_);
                                v___x_2809_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2808_);
                                if v___x_2809_ == 0 {
                                    v___x_2810_ =
                                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__47;
                                    lean_inc(v___x_2803_);
                                    v___x_2811_ = l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2810_);
                                    if v___x_2811_ == 0 {
                                        v___x_2812_ =
                                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__49;
                                        v___x_2813_ =
                                            l_Lean_Syntax_isOfKind(v___x_2803_, v___x_2812_);
                                        if v___x_2813_ == 0 {
                                            lean_dec(v_attrs_x3f_2790_);
                                            lean_dec(v___y_2789_);
                                            lean_dec(v_stx_1648_);
                                            v___x_2814_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2814_;
                                        } else {
                                            v___x_2815_ = lean_unsigned_to_nat(4);
                                            v___x_2816_ =
                                                l_Lean_Syntax_getArg(v_stx_1648_, v___x_2815_);
                                            v___x_2817_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                            lean_inc(v___x_2816_);
                                            v___x_2818_ =
                                                l_Lean_Syntax_isOfKind(v___x_2816_, v___x_2817_);
                                            if v___x_2818_ == 0 {
                                                lean_dec(v___x_2816_);
                                                lean_dec(v_attrs_x3f_2790_);
                                                lean_dec(v___y_2789_);
                                                lean_dec(v_stx_1648_);
                                                v___x_2819_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v___y_2792_,
                                                    );
                                                return v___x_2819_;
                                            } else {
                                                v___x_2820_ =
                                                    l_Lean_Syntax_getArg(v___x_2816_, v___y_2788_);
                                                lean_dec(v___x_2816_);
                                                v___x_2821_ = lean_unsigned_to_nat(5);
                                                v___x_2822_ =
                                                    l_Lean_Syntax_getArg(v_stx_1648_, v___x_2821_);
                                                v___x_2823_ = l_Lean_Syntax_isNone(v___x_2822_);
                                                if v___x_2823_ == 0 {
                                                    lean_inc(v___x_2822_);
                                                    v___x_2824_ = l_Lean_Syntax_matchesNull(
                                                        v___x_2822_,
                                                        v___y_2788_,
                                                    );
                                                    if v___x_2824_ == 0 {
                                                        lean_dec(v___x_2822_);
                                                        lean_dec(v___x_2820_);
                                                        lean_dec(v_attrs_x3f_2790_);
                                                        lean_dec(v___y_2789_);
                                                        lean_dec(v_stx_1648_);
                                                        v___x_2825_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v___y_2792_,
                                                            );
                                                        return v___x_2825_;
                                                    } else {
                                                        v___x_2826_ = l_Lean_Syntax_getArg(
                                                            v___x_2822_,
                                                            v___x_1926_,
                                                        );
                                                        lean_dec(v___x_2822_);
                                                        v___x_2827_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                                        lean_inc(v___x_2826_);
                                                        v___x_2828_ = l_Lean_Syntax_isOfKind(
                                                            v___x_2826_,
                                                            v___x_2827_,
                                                        );
                                                        if v___x_2828_ == 0 {
                                                            lean_dec(v___x_2826_);
                                                            lean_dec(v___x_2820_);
                                                            lean_dec(v_attrs_x3f_2790_);
                                                            lean_dec(v___y_2789_);
                                                            lean_dec(v_stx_1648_);
                                                            v___x_2829_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                                            return v___x_2829_;
                                                        } else {
                                                            v_name_2830_ = l_Lean_Syntax_getArg(
                                                                v___x_2826_,
                                                                v___x_2802_,
                                                            );
                                                            lean_dec(v___x_2826_);
                                                            v___x_2831_ =
                                                                lean_alloc_ctor(1, 1, (0) as u32);
                                                            lean_ctor_set(
                                                                v___x_2831_,
                                                                0,
                                                                v_name_2830_,
                                                            );
                                                            v___y_2062_ = v___y_2788_;
                                                            v___y_2063_ = v___x_2796_;
                                                            v___y_2064_ = v___x_2811_;
                                                            v___y_2065_ = v_attrs_x3f_2790_;
                                                            v___y_2066_ = v___x_2817_;
                                                            v___y_2067_ = v___x_2802_;
                                                            v___y_2068_ = v___y_2789_;
                                                            v___y_2069_ = v___x_2795_;
                                                            v___y_2070_ = v___x_2820_;
                                                            v_name_2071_ = v___x_2831_;
                                                            v___y_2072_ = v___y_2791_;
                                                            v___y_2073_ = v___y_2792_;
                                                            state = 10;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v___x_2822_);
                                                    v___x_2832_ = lean_box(0);
                                                    v___y_2062_ = v___y_2788_;
                                                    v___y_2063_ = v___x_2796_;
                                                    v___y_2064_ = v___x_2811_;
                                                    v___y_2065_ = v_attrs_x3f_2790_;
                                                    v___y_2066_ = v___x_2817_;
                                                    v___y_2067_ = v___x_2802_;
                                                    v___y_2068_ = v___y_2789_;
                                                    v___y_2069_ = v___x_2795_;
                                                    v___y_2070_ = v___x_2820_;
                                                    v_name_2071_ = v___x_2832_;
                                                    v___y_2072_ = v___y_2791_;
                                                    v___y_2073_ = v___y_2792_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_2803_);
                                        v___x_2833_ = lean_unsigned_to_nat(4);
                                        v___x_2834_ =
                                            l_Lean_Syntax_getArg(v_stx_1648_, v___x_2833_);
                                        v___x_2835_ =
                                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                        lean_inc(v___x_2834_);
                                        v___x_2836_ =
                                            l_Lean_Syntax_isOfKind(v___x_2834_, v___x_2835_);
                                        if v___x_2836_ == 0 {
                                            lean_dec(v___x_2834_);
                                            lean_dec(v_attrs_x3f_2790_);
                                            lean_dec(v___y_2789_);
                                            lean_dec(v_stx_1648_);
                                            v___x_2837_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2837_;
                                        } else {
                                            v___x_2838_ =
                                                l_Lean_Syntax_getArg(v___x_2834_, v___y_2788_);
                                            lean_dec(v___x_2834_);
                                            v___x_2839_ = lean_unsigned_to_nat(5);
                                            v___x_2840_ =
                                                l_Lean_Syntax_getArg(v_stx_1648_, v___x_2839_);
                                            v___x_2841_ = l_Lean_Syntax_isNone(v___x_2840_);
                                            if v___x_2841_ == 0 {
                                                lean_inc(v___x_2840_);
                                                v___x_2842_ = l_Lean_Syntax_matchesNull(
                                                    v___x_2840_,
                                                    v___y_2788_,
                                                );
                                                if v___x_2842_ == 0 {
                                                    lean_dec(v___x_2840_);
                                                    lean_dec(v___x_2838_);
                                                    lean_dec(v_attrs_x3f_2790_);
                                                    lean_dec(v___y_2789_);
                                                    lean_dec(v_stx_1648_);
                                                    v___x_2843_ =
                                                        l_Lean_Macro_throwUnsupported___redArg(
                                                            v___y_2792_,
                                                        );
                                                    return v___x_2843_;
                                                } else {
                                                    v___x_2844_ = l_Lean_Syntax_getArg(
                                                        v___x_2840_,
                                                        v___x_1926_,
                                                    );
                                                    lean_dec(v___x_2840_);
                                                    v___x_2845_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                                    lean_inc(v___x_2844_);
                                                    v___x_2846_ = l_Lean_Syntax_isOfKind(
                                                        v___x_2844_,
                                                        v___x_2845_,
                                                    );
                                                    if v___x_2846_ == 0 {
                                                        lean_dec(v___x_2844_);
                                                        lean_dec(v___x_2838_);
                                                        lean_dec(v_attrs_x3f_2790_);
                                                        lean_dec(v___y_2789_);
                                                        lean_dec(v_stx_1648_);
                                                        v___x_2847_ =
                                                            l_Lean_Macro_throwUnsupported___redArg(
                                                                v___y_2792_,
                                                            );
                                                        return v___x_2847_;
                                                    } else {
                                                        v_name_2848_ = l_Lean_Syntax_getArg(
                                                            v___x_2844_,
                                                            v___x_2802_,
                                                        );
                                                        lean_dec(v___x_2844_);
                                                        v___x_2849_ =
                                                            lean_alloc_ctor(1, 1, (0) as u32);
                                                        lean_ctor_set(v___x_2849_, 0, v_name_2848_);
                                                        v___y_2221_ = v___y_2788_;
                                                        v___y_2222_ = v___x_2796_;
                                                        v___y_2223_ = v___x_2838_;
                                                        v___y_2224_ = v_attrs_x3f_2790_;
                                                        v___y_2225_ = v___x_2809_;
                                                        v___y_2226_ = v___x_2802_;
                                                        v___y_2227_ = v___y_2789_;
                                                        v___y_2228_ = v___x_2795_;
                                                        v___y_2229_ = v___x_2835_;
                                                        v_name_2230_ = v___x_2849_;
                                                        v___y_2231_ = v___y_2791_;
                                                        v___y_2232_ = v___y_2792_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v___x_2840_);
                                                v___x_2850_ = lean_box(0);
                                                v___y_2221_ = v___y_2788_;
                                                v___y_2222_ = v___x_2796_;
                                                v___y_2223_ = v___x_2838_;
                                                v___y_2224_ = v_attrs_x3f_2790_;
                                                v___y_2225_ = v___x_2809_;
                                                v___y_2226_ = v___x_2802_;
                                                v___y_2227_ = v___y_2789_;
                                                v___y_2228_ = v___x_2795_;
                                                v___y_2229_ = v___x_2835_;
                                                v_name_2230_ = v___x_2850_;
                                                v___y_2231_ = v___y_2791_;
                                                v___y_2232_ = v___y_2792_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v___x_2803_);
                                    v___x_2851_ = lean_unsigned_to_nat(4);
                                    v___x_2852_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2851_);
                                    v___x_2853_ =
                                        l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                    lean_inc(v___x_2852_);
                                    v___x_2854_ = l_Lean_Syntax_isOfKind(v___x_2852_, v___x_2853_);
                                    if v___x_2854_ == 0 {
                                        lean_dec(v___x_2852_);
                                        lean_dec(v_attrs_x3f_2790_);
                                        lean_dec(v___y_2789_);
                                        lean_dec(v_stx_1648_);
                                        v___x_2855_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                        return v___x_2855_;
                                    } else {
                                        v___x_2856_ =
                                            l_Lean_Syntax_getArg(v___x_2852_, v___y_2788_);
                                        lean_dec(v___x_2852_);
                                        v___x_2857_ = lean_unsigned_to_nat(5);
                                        v___x_2858_ =
                                            l_Lean_Syntax_getArg(v_stx_1648_, v___x_2857_);
                                        v___x_2859_ = l_Lean_Syntax_isNone(v___x_2858_);
                                        if v___x_2859_ == 0 {
                                            lean_inc(v___x_2858_);
                                            v___x_2860_ =
                                                l_Lean_Syntax_matchesNull(v___x_2858_, v___y_2788_);
                                            if v___x_2860_ == 0 {
                                                lean_dec(v___x_2858_);
                                                lean_dec(v___x_2856_);
                                                lean_dec(v_attrs_x3f_2790_);
                                                lean_dec(v___y_2789_);
                                                lean_dec(v_stx_1648_);
                                                v___x_2861_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v___y_2792_,
                                                    );
                                                return v___x_2861_;
                                            } else {
                                                v___x_2862_ =
                                                    l_Lean_Syntax_getArg(v___x_2858_, v___x_1926_);
                                                lean_dec(v___x_2858_);
                                                v___x_2863_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                                lean_inc(v___x_2862_);
                                                v___x_2864_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2862_,
                                                    v___x_2863_,
                                                );
                                                if v___x_2864_ == 0 {
                                                    lean_dec(v___x_2862_);
                                                    lean_dec(v___x_2856_);
                                                    lean_dec(v_attrs_x3f_2790_);
                                                    lean_dec(v___y_2789_);
                                                    lean_dec(v_stx_1648_);
                                                    v___x_2865_ =
                                                        l_Lean_Macro_throwUnsupported___redArg(
                                                            v___y_2792_,
                                                        );
                                                    return v___x_2865_;
                                                } else {
                                                    v_name_2866_ = l_Lean_Syntax_getArg(
                                                        v___x_2862_,
                                                        v___x_2802_,
                                                    );
                                                    lean_dec(v___x_2862_);
                                                    v___x_2867_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                    lean_ctor_set(v___x_2867_, 0, v_name_2866_);
                                                    v___y_2402_ = v___y_2788_;
                                                    v___y_2403_ = v___x_2807_;
                                                    v___y_2404_ = v___x_2796_;
                                                    v___y_2405_ = v___x_2856_;
                                                    v___y_2406_ = v_attrs_x3f_2790_;
                                                    v___y_2407_ = v___x_2802_;
                                                    v___y_2408_ = v___x_2853_;
                                                    v___y_2409_ = v___y_2789_;
                                                    v___y_2410_ = v___x_2795_;
                                                    v_name_2411_ = v___x_2867_;
                                                    v___y_2412_ = v___y_2791_;
                                                    v___y_2413_ = v___y_2792_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v___x_2858_);
                                            v___x_2868_ = lean_box(0);
                                            v___y_2402_ = v___y_2788_;
                                            v___y_2403_ = v___x_2807_;
                                            v___y_2404_ = v___x_2796_;
                                            v___y_2405_ = v___x_2856_;
                                            v___y_2406_ = v_attrs_x3f_2790_;
                                            v___y_2407_ = v___x_2802_;
                                            v___y_2408_ = v___x_2853_;
                                            v___y_2409_ = v___y_2789_;
                                            v___y_2410_ = v___x_2795_;
                                            v_name_2411_ = v___x_2868_;
                                            v___y_2412_ = v___y_2791_;
                                            v___y_2413_ = v___y_2792_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v___x_2803_);
                                v___x_2869_ = lean_unsigned_to_nat(4);
                                v___x_2870_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2869_);
                                v___x_2871_ =
                                    l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                                lean_inc(v___x_2870_);
                                v___x_2872_ = l_Lean_Syntax_isOfKind(v___x_2870_, v___x_2871_);
                                if v___x_2872_ == 0 {
                                    lean_dec(v___x_2870_);
                                    lean_dec(v_attrs_x3f_2790_);
                                    lean_dec(v___y_2789_);
                                    lean_dec(v_stx_1648_);
                                    v___x_2873_ =
                                        l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                    return v___x_2873_;
                                } else {
                                    v___x_2874_ = l_Lean_Syntax_getArg(v___x_2870_, v___y_2788_);
                                    lean_dec(v___x_2870_);
                                    v___x_2875_ = lean_unsigned_to_nat(5);
                                    v___x_2876_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2875_);
                                    v___x_2877_ = l_Lean_Syntax_isNone(v___x_2876_);
                                    if v___x_2877_ == 0 {
                                        lean_inc(v___x_2876_);
                                        v___x_2878_ =
                                            l_Lean_Syntax_matchesNull(v___x_2876_, v___y_2788_);
                                        if v___x_2878_ == 0 {
                                            lean_dec(v___x_2876_);
                                            lean_dec(v___x_2874_);
                                            lean_dec(v_attrs_x3f_2790_);
                                            lean_dec(v___y_2789_);
                                            lean_dec(v_stx_1648_);
                                            v___x_2879_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2879_;
                                        } else {
                                            v___x_2880_ =
                                                l_Lean_Syntax_getArg(v___x_2876_, v___x_1926_);
                                            lean_dec(v___x_2876_);
                                            v___x_2881_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                            lean_inc(v___x_2880_);
                                            v___x_2882_ =
                                                l_Lean_Syntax_isOfKind(v___x_2880_, v___x_2881_);
                                            if v___x_2882_ == 0 {
                                                lean_dec(v___x_2880_);
                                                lean_dec(v___x_2874_);
                                                lean_dec(v_attrs_x3f_2790_);
                                                lean_dec(v___y_2789_);
                                                lean_dec(v_stx_1648_);
                                                v___x_2883_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v___y_2792_,
                                                    );
                                                return v___x_2883_;
                                            } else {
                                                v_name_2884_ =
                                                    l_Lean_Syntax_getArg(v___x_2880_, v___x_2802_);
                                                lean_dec(v___x_2880_);
                                                v___x_2885_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_2885_, 0, v_name_2884_);
                                                v___y_2583_ = v___y_2788_;
                                                v___y_2584_ = v___x_2871_;
                                                v___y_2585_ = v___x_2796_;
                                                v___y_2586_ = v___x_2874_;
                                                v___y_2587_ = v___x_2805_;
                                                v___y_2588_ = v_attrs_x3f_2790_;
                                                v___y_2589_ = v___x_2802_;
                                                v___y_2590_ = v___y_2789_;
                                                v___y_2591_ = v___x_2795_;
                                                v_name_2592_ = v___x_2885_;
                                                v___y_2593_ = v___y_2791_;
                                                v___y_2594_ = v___y_2792_;
                                                state = 29;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_2876_);
                                        v___x_2886_ = lean_box(0);
                                        v___y_2583_ = v___y_2788_;
                                        v___y_2584_ = v___x_2871_;
                                        v___y_2585_ = v___x_2796_;
                                        v___y_2586_ = v___x_2874_;
                                        v___y_2587_ = v___x_2805_;
                                        v___y_2588_ = v_attrs_x3f_2790_;
                                        v___y_2589_ = v___x_2802_;
                                        v___y_2590_ = v___y_2789_;
                                        v___y_2591_ = v___x_2795_;
                                        v_name_2592_ = v___x_2886_;
                                        v___y_2593_ = v___y_2791_;
                                        v___y_2594_ = v___y_2792_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v___x_2803_);
                            v___x_2887_ = lean_unsigned_to_nat(4);
                            v___x_2888_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2887_);
                            v___x_2889_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__51;
                            lean_inc(v___x_2888_);
                            v___x_2890_ = l_Lean_Syntax_isOfKind(v___x_2888_, v___x_2889_);
                            if v___x_2890_ == 0 {
                                lean_dec(v___x_2888_);
                                lean_dec(v_attrs_x3f_2790_);
                                lean_dec(v___y_2789_);
                                lean_dec(v_stx_1648_);
                                v___x_2891_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                return v___x_2891_;
                            } else {
                                v___x_2892_ = l_Lean_Syntax_getArg(v___x_2888_, v___y_2788_);
                                lean_dec(v___x_2888_);
                                v___x_2893_ = lean_unsigned_to_nat(5);
                                v___x_2894_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2893_);
                                v___x_2895_ = l_Lean_Syntax_isNone(v___x_2894_);
                                if v___x_2895_ == 0 {
                                    lean_inc(v___x_2894_);
                                    v___x_2896_ =
                                        l_Lean_Syntax_matchesNull(v___x_2894_, v___y_2788_);
                                    if v___x_2896_ == 0 {
                                        lean_dec(v___x_2894_);
                                        lean_dec(v___x_2892_);
                                        lean_dec(v_attrs_x3f_2790_);
                                        lean_dec(v___y_2789_);
                                        lean_dec(v_stx_1648_);
                                        v___x_2897_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                        return v___x_2897_;
                                    } else {
                                        v___x_2898_ =
                                            l_Lean_Syntax_getArg(v___x_2894_, v___x_1926_);
                                        lean_dec(v___x_2894_);
                                        v___x_2899_ =
                                            l_Lean_Elab_Command_expandMixfix___lam__0___closed__27;
                                        lean_inc(v___x_2898_);
                                        v___x_2900_ =
                                            l_Lean_Syntax_isOfKind(v___x_2898_, v___x_2899_);
                                        if v___x_2900_ == 0 {
                                            lean_dec(v___x_2898_);
                                            lean_dec(v___x_2892_);
                                            lean_dec(v_attrs_x3f_2790_);
                                            lean_dec(v___y_2789_);
                                            lean_dec(v_stx_1648_);
                                            v___x_2901_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v___y_2792_);
                                            return v___x_2901_;
                                        } else {
                                            v_name_2902_ =
                                                l_Lean_Syntax_getArg(v___x_2898_, v___x_2802_);
                                            lean_dec(v___x_2898_);
                                            v___x_2903_ = lean_alloc_ctor(1, 1, (0) as u32);
                                            lean_ctor_set(v___x_2903_, 0, v_name_2902_);
                                            v___y_2764_ = v___y_2788_;
                                            v___y_2765_ = v___x_2796_;
                                            v___y_2766_ = v___x_2892_;
                                            v___y_2767_ = v_attrs_x3f_2790_;
                                            v___y_2768_ = v___x_2802_;
                                            v___y_2769_ = v___x_2889_;
                                            v___y_2770_ = v___y_2789_;
                                            v___y_2771_ = v___x_2795_;
                                            v_name_2772_ = v___x_2903_;
                                            v___y_2773_ = v___y_2791_;
                                            v___y_2774_ = v___y_2792_;
                                            state = 36;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v___x_2894_);
                                    v___x_2904_ = lean_box(0);
                                    v___y_2764_ = v___y_2788_;
                                    v___y_2765_ = v___x_2796_;
                                    v___y_2766_ = v___x_2892_;
                                    v___y_2767_ = v_attrs_x3f_2790_;
                                    v___y_2768_ = v___x_2802_;
                                    v___y_2769_ = v___x_2889_;
                                    v___y_2770_ = v___y_2789_;
                                    v___y_2771_ = v___x_2795_;
                                    v_name_2772_ = v___x_2904_;
                                    v___y_2773_ = v___y_2791_;
                                    v___y_2774_ = v___y_2792_;
                                    state = 36;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            38 => {
                v___x_2909_ = lean_unsigned_to_nat(1);
                v___x_2910_ = l_Lean_Syntax_getArg(v_stx_1648_, v___x_2909_);
                v___x_2911_ = l_Lean_Syntax_isNone(v___x_2910_);
                if v___x_2911_ == 0 {
                    lean_inc(v___x_2910_);
                    v___x_2912_ = l_Lean_Syntax_matchesNull(v___x_2910_, v___x_2909_);
                    if v___x_2912_ == 0 {
                        lean_dec(v___x_2910_);
                        lean_dec(v_doc_x3f_2906_);
                        lean_dec(v_stx_1648_);
                        v___x_2913_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2908_);
                        return v___x_2913_;
                    } else {
                        v___x_2914_ = l_Lean_Syntax_getArg(v___x_2910_, v___x_1926_);
                        lean_dec(v___x_2910_);
                        v___x_2915_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__52;
                        lean_inc(v___x_2914_);
                        v___x_2916_ = l_Lean_Syntax_isOfKind(v___x_2914_, v___x_2915_);
                        if v___x_2916_ == 0 {
                            lean_dec(v___x_2914_);
                            lean_dec(v_doc_x3f_2906_);
                            lean_dec(v_stx_1648_);
                            v___x_2917_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2908_);
                            return v___x_2917_;
                        } else {
                            v___x_2918_ = l_Lean_Syntax_getArg(v___x_2914_, v___x_2909_);
                            lean_dec(v___x_2914_);
                            v_attrs_x3f_2919_ = l_Lean_Syntax_getArgs(v___x_2918_);
                            lean_dec(v___x_2918_);
                            v___x_2920_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2920_, 0, v_attrs_x3f_2919_);
                            v___y_2788_ = v___x_2909_;
                            v___y_2789_ = v_doc_x3f_2906_;
                            v_attrs_x3f_2790_ = v___x_2920_;
                            v___y_2791_ = v___y_2907_;
                            v___y_2792_ = v___y_2908_;
                            state = 37;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2910_);
                    v___x_2921_ = lean_box(0);
                    v___y_2788_ = v___x_2909_;
                    v___y_2789_ = v_doc_x3f_2906_;
                    v_attrs_x3f_2790_ = v___x_2921_;
                    v___y_2791_ = v___y_2907_;
                    v___y_2792_ = v___y_2908_;
                    state = 37;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix___lam__0___boxed(
    mut v_stx_2933_: *mut LeanObject,
    mut v___y_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2936_: *mut LeanObject = core::ptr::null_mut();
    v_res_2936_ = l_Lean_Elab_Command_expandMixfix___lam__0(v_stx_2933_, v___y_2934_, v___y_2935_);
    lean_dec_ref(v___y_2934_);
    return v_res_2936_;
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix(
    mut v_stx_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    v___f_2941_ = l_Lean_Elab_Command_expandMixfix___closed__0;
    v___x_2942_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix_withAttrKindGlobal(
        v_stx_2938_,
        v___f_2941_,
        v_a_2939_,
        v_a_2940_,
    );
    return v___x_2942_;
}
pub unsafe fn l_Lean_Elab_Command_expandMixfix___boxed(
    mut v_stx_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2946_: *mut LeanObject = core::ptr::null_mut();
    v_res_2946_ = l_Lean_Elab_Command_expandMixfix(v_stx_2943_, v_a_2944_, v_a_2945_);
    lean_dec_ref(v_a_2944_);
    return v_res_2946_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1()
-> *mut LeanObject {
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    v___x_2955_ = l_Lean_Elab_macroAttribute;
    v___x_2956_ = l_Lean_Elab_Command_expandMixfix___lam__0___closed__17;
    v___x_2957_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2;
    v___x_2958_ = lean_alloc_closure(
        l_Lean_Elab_Command_expandMixfix___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_2959_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2955_,
        v___x_2956_,
        v___x_2957_,
        v___x_2958_,
    );
    return v___x_2959_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___boxed(
    mut v_a_2960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2961_: *mut LeanObject = core::ptr::null_mut();
    v_res_2961_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
    return v_res_2961_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3()
-> *mut LeanObject {
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    v___x_2988_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1___closed__2;
    v___x_2989_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___closed__6;
    v___x_2990_ = l_Lean_addBuiltinDeclarationRanges(v___x_2988_, v___x_2989_);
    return v___x_2990_;
}
pub unsafe fn l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3___boxed(
    mut v_a_2991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2992_: *mut LeanObject = core::ptr::null_mut();
    v_res_2992_ = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
    return v_res_2992_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Mixfix(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Mixfix_0__Lean_Elab_Command_expandMixfix___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Mixfix(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Mixfix(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Mixfix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Mixfix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Mixfix(builtin);
}
