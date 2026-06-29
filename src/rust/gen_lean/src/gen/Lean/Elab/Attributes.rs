// Lean compiler output
// Module: Lean.Elab.Attributes
// Imports: Lean.Elab.Util Lean.Compiler.InitAttr Lean.Parser.Term Init.Data.Format.Macro
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_push,
    lean_array_size, lean_name_eq, lean_nat_dec_lt, lean_nat_to_int, lean_string_length,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getSepArgs, l_Lean_Syntax_isNone, l_Lean_expandMacros,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Macro_getCurrNamespace, l_Lean_Name_str___override, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getId, l_Lean_Syntax_getKind, l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_ParametricAttribute_getParam_x3f___redArg, l_Lean_getAttributeImpl,
};
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, l_Lean_regularInitAttr,
    runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Elab::Util::{
    initialize_Lean_Elab_Util, l_Lean_Elab_liftMacroM___redArg, l_Lean_Elab_logException___redArg,
    runtime_initialize_Lean_Elab_Util,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_instInhabitedEffectiveImport_default, l_Lean_withoutExporting___redArg,
};
use crate::r#gen::Lean::Exception::{l_Lean_throwError___redArg, l_Lean_throwErrorAt___redArg};
use crate::r#gen::Lean::ExtraModUses::l_Lean_recordExtraModUseFromDecl___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, runtime_initialize_Lean_Parser_Term,
};
pub static l_Lean_Elab_instInhabitedAttribute_default___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedAttribute_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedAttribute_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedAttribute_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedAttribute_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedAttribute: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedAttribute_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToFormatAttribute___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToFormatAttribute___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instToFormatAttribute___lam__0___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToFormatAttribute___lam__0___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToFormatAttribute___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToFormatAttribute___lam__0___closed__7_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [108, 111, 99, 97, 108, 32, 0],
};
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToFormatAttribute___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 99, 111, 112, 101, 100, 32, 0],
};
static mut l_Lean_Elab_instToFormatAttribute___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instToFormatAttribute___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_instToFormatAttribute___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instToFormatAttribute___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instToFormatAttribute: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instToFormatAttribute___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_toAttributeKind___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_toAttributeKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_toAttributeKind___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_toAttributeKind___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_toAttributeKind___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_toAttributeKind___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_toAttributeKind___closed__3_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [115, 99, 111, 112, 101, 100, 0],
    };
static mut l_Lean_Elab_toAttributeKind___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_toAttributeKind___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_toAttributeKind___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_toAttributeKind___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_toAttributeKind___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__3_value)
                as *mut crate::leanh::LeanObject,
            10992023688825480391 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_toAttributeKind___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_toAttributeKind___closed__5_value: crate::leanh::LeanStringObject<49> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 49,
        m_capacity: 49,
        m_length: 48,
        m_data: [
            83, 99, 111, 112, 101, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 32,
            109, 117, 115, 116, 32, 98, 101, 32, 117, 115, 101, 100, 32, 105, 110, 115, 105, 100,
            101, 32, 110, 97, 109, 101, 115, 112, 97, 99, 101, 115, 0,
        ],
    };
static mut l_Lean_Elab_toAttributeKind___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkAttrKindGlobal___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_mkAttrKindGlobal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_mkAttrKindGlobal___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7983999284776576032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkAttrKindGlobal___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkAttrKindGlobal___closed__2_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_mkAttrKindGlobal___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkAttrKindGlobal___closed__3_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_mkAttrKindGlobal___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkAttrKindGlobal___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__3_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkAttrKindGlobal___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkAttrKindGlobal___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkAttrKindGlobal___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkAttrKindGlobal___closed__6_value: crate::leanh::LeanArrayObject<1> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkAttrKindGlobal___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkAttrKindGlobal___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_mkAttrKindGlobal___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_mkAttrKindGlobal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkAttrKindGlobal___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabAttr___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16173796135615239867 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabAttr___redArg___lam__5___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 97, 116, 116, 114, 105, 98, 117, 116,
        101, 32, 96, 91, 0,
    ],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabAttr___redArg___lam__5___closed__2_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [93, 96, 58, 32, 109, 111, 100, 117, 108, 101, 32, 96, 0],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__5___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabAttr___redArg___lam__5___closed__4_value:
    crate::leanh::LeanStringObject<85> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 85,
    m_capacity: 85,
    m_length: 84,
    m_data: [
        96, 32, 105, 115, 32, 108, 111, 97, 100, 101, 100, 32, 102, 111, 114, 32, 73, 82, 32, 111,
        110, 108, 121, 32, 40, 114, 101, 97, 99, 104, 101, 100, 32, 97, 115, 32, 97, 32, 112, 114,
        105, 118, 97, 116, 101, 32, 96, 109, 101, 116, 97, 96, 32, 100, 101, 112, 101, 110, 100,
        101, 110, 99, 121, 41, 46, 32, 65, 100, 100, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116,
        32, 111, 102, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__5___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabAttr___redArg___lam__5___closed__6_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [96, 46, 0],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__5___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabAttr___redArg___lam__5___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabAttr___redArg___lam__8___closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        85, 110, 107, 110, 111, 119, 110, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96,
        91, 0,
    ],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__8___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabAttr___redArg___lam__8___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabAttr___redArg___lam__8___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [93, 96, 0],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__8___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__8___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabAttr___redArg___lam__8___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabAttr___redArg___lam__13___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [65, 116, 116, 114, 0],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__13___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabAttr___redArg___lam__13___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 105, 109, 112, 108, 101, 0],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__13___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_toAttributeKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4584992172905639687 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__1_value)
            as *mut crate::leanh::LeanObject,
        3878072352281346923 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__13___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabAttr___redArg___lam__13___closed__3_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        85, 110, 107, 110, 111, 119, 110, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Elab_elabAttr___redArg___lam__13___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabAttr___redArg___lam__13___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_elabAttr___redArg___lam__13___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabAttr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_elabAttr___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_elabAttr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabAttrs___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_elabAttrs___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabAttrs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = l_Lean_Elab_instToFormatAttribute___lam__0___closed__0;
    v___x_736_ = lean_string_length(v___x_735_);
    return v___x_736_;
}
pub unsafe fn _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__2_once),
        _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__2,
    );
    v___x_738_ = lean_nat_to_int(v___x_737_);
    return v___x_738_;
}
pub unsafe fn l_Lean_Elab_instToFormatAttribute___lam__0(
    mut v_attr_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_747_: u8 = 0;
    let mut v_name_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: u8 = 0;
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: u8 = 0;
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_747_ = crate::leanh::lean_ctor_get_uint8(
                    v_attr_746_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_name_748_ = crate::leanh::lean_ctor_get(v_attr_746_, 0);
                crate::leanh::lean_inc(v_name_748_);
                v_stx_749_ = crate::leanh::lean_ctor_get(v_attr_746_, 1);
                crate::leanh::lean_inc(v_stx_749_);
                crate::leanh::lean_dec_ref(v_attr_746_);
                match v_kind_747_ {
                    0 => {
                        v___x_773_ = l_Lean_Elab_instToFormatAttribute___lam__0___closed__6;
                        v___y_751_ = v___x_773_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_774_ = l_Lean_Elab_instToFormatAttribute___lam__0___closed__7;
                        v___y_751_ = v___x_774_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_775_ = l_Lean_Elab_instToFormatAttribute___lam__0___closed__8;
                        v___y_751_ = v___x_775_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_751_);
                v___x_752_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_752_, 0, v___y_751_);
                v___x_753_ = 1;
                v___x_754_ = l_Lean_Name_toString(v_name_748_, v___x_753_);
                v___x_755_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_755_, 0, v___x_754_);
                v___x_756_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_756_, 0, v___x_752_);
                crate::leanh::lean_ctor_set(v___x_756_, 1, v___x_755_);
                v___x_757_ = crate::leanh::lean_box(0);
                v___x_758_ = 0;
                v___x_759_ = l_Lean_Syntax_formatStx(v_stx_749_, v___x_757_, v___x_758_);
                v___x_760_ = l_Std_Format_defWidth;
                v___x_761_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_762_ = l_Std_Format_pretty(v___x_759_, v___x_760_, v___x_761_, v___x_761_);
                v___x_763_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_763_, 0, v___x_762_);
                v___x_764_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_764_, 0, v___x_756_);
                crate::leanh::lean_ctor_set(v___x_764_, 1, v___x_763_);
                v___x_765_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_instToFormatAttribute___lam__0___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_instToFormatAttribute___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Elab_instToFormatAttribute___lam__0___closed__3,
                );
                v___x_766_ = l_Lean_Elab_instToFormatAttribute___lam__0___closed__4;
                v___x_767_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_767_, 0, v___x_766_);
                crate::leanh::lean_ctor_set(v___x_767_, 1, v___x_764_);
                v___x_768_ = l_Lean_Elab_instToFormatAttribute___lam__0___closed__5;
                v___x_769_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_769_, 0, v___x_767_);
                crate::leanh::lean_ctor_set(v___x_769_, 1, v___x_768_);
                v___x_770_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_770_, 0, v___x_765_);
                crate::leanh::lean_ctor_set(v___x_770_, 1, v___x_769_);
                v___x_771_ = 0;
                v___x_772_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_770_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_772_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_771_,
                );
                return v___x_772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_toAttributeKind(
    mut v_attrKindStx_788_: *mut crate::leanh::LeanObject,
    mut v_a_789_: *mut crate::leanh::LeanObject,
    mut v_a_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: u8 = 0;
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: u8 = 0;
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_806_: u8 = 0;
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: u8 = 0;
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_819_: u8 = 0;
    let mut v_a_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_824_: u8 = 0;
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_828_: u8 = 0;
    let mut v___x_829_: u8 = 0;
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_791_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_792_ = l_Lean_Syntax_getArg(v_attrKindStx_788_, v___x_791_);
                v___x_793_ = l_Lean_Syntax_isNone(v___x_792_);
                if v___x_793_ == 0 {
                    v___x_794_ = l_Lean_Syntax_getArg(v___x_792_, v___x_791_);
                    crate::leanh::lean_dec(v___x_792_);
                    v___x_795_ = l_Lean_Syntax_getKind(v___x_794_);
                    v___x_796_ = l_Lean_Elab_toAttributeKind___closed__4;
                    v___x_797_ = lean_name_eq(v___x_795_, v___x_796_);
                    crate::leanh::lean_dec(v___x_795_);
                    if v___x_797_ == 0 {
                        v___x_798_ = 1;
                        v___x_799_ = crate::leanh::lean_box((v___x_798_) as usize);
                        v___x_800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_800_, 0, v___x_799_);
                        crate::leanh::lean_ctor_set(v___x_800_, 1, v_a_790_);
                        return v___x_800_;
                    } else {
                        v___x_801_ = l_Lean_Macro_getCurrNamespace(v_a_789_, v_a_790_);
                        if crate::leanh::lean_obj_tag(v___x_801_) == 0 {
                            v_a_802_ = crate::leanh::lean_ctor_get(v___x_801_, 0);
                            v_a_803_ = crate::leanh::lean_ctor_get(v___x_801_, 1);
                            v_isSharedCheck_819_ =
                                (!crate::leanh::lean_is_exclusive(v___x_801_)) as u8;
                            if v_isSharedCheck_819_ == 0 {
                                v___x_805_ = v___x_801_;
                                v_isShared_806_ = v_isSharedCheck_819_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_803_);
                                crate::leanh::lean_inc(v_a_802_);
                                crate::leanh::lean_dec(v___x_801_);
                                v___x_805_ = crate::leanh::lean_box(0);
                                v_isShared_806_ = v_isSharedCheck_819_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_820_ = crate::leanh::lean_ctor_get(v___x_801_, 0);
                            v_a_821_ = crate::leanh::lean_ctor_get(v___x_801_, 1);
                            v_isSharedCheck_828_ =
                                (!crate::leanh::lean_is_exclusive(v___x_801_)) as u8;
                            if v_isSharedCheck_828_ == 0 {
                                v___x_823_ = v___x_801_;
                                v_isShared_824_ = v_isSharedCheck_828_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_821_);
                                crate::leanh::lean_inc(v_a_820_);
                                crate::leanh::lean_dec(v___x_801_);
                                v___x_823_ = crate::leanh::lean_box(0);
                                v_isShared_824_ = v_isSharedCheck_828_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_792_);
                    v___x_829_ = 0;
                    v___x_830_ = crate::leanh::lean_box((v___x_829_) as usize);
                    v___x_831_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_831_, 0, v___x_830_);
                    crate::leanh::lean_ctor_set(v___x_831_, 1, v_a_790_);
                    return v___x_831_;
                }
            }
            1 => {
                v___x_807_ = l_Lean_Name_isAnonymous(v_a_802_);
                crate::leanh::lean_dec(v_a_802_);
                if v___x_807_ == 0 {
                    v___x_808_ = 2;
                    v___x_809_ = crate::leanh::lean_box((v___x_808_) as usize);
                    if v_isShared_806_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_805_, 0, v___x_809_);
                        v___x_811_ = v___x_805_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_812_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 1, v_a_803_);
                        v___x_811_ = v_reuseFailAlloc_812_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_ref_813_ = crate::leanh::lean_ctor_get(v_a_789_, 5);
                    v___x_814_ = l_Lean_Elab_toAttributeKind___closed__5;
                    crate::leanh::lean_inc(v_ref_813_);
                    v___x_815_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_815_, 0, v_ref_813_);
                    crate::leanh::lean_ctor_set(v___x_815_, 1, v___x_814_);
                    if v_isShared_806_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_805_, 1);
                        crate::leanh::lean_ctor_set(v___x_805_, 0, v___x_815_);
                        v___x_817_ = v___x_805_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_818_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_818_, 1, v_a_803_);
                        v___x_817_ = v_reuseFailAlloc_818_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_811_;
            }
            3 => {
                return v___x_817_;
            }
            4 => {
                if v_isShared_824_ == 0 {
                    v___x_826_ = v___x_823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_827_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 1, v_a_821_);
                    v___x_826_ = v_reuseFailAlloc_827_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_toAttributeKind___boxed(
    mut v_attrKindStx_832_: *mut crate::leanh::LeanObject,
    mut v_a_833_: *mut crate::leanh::LeanObject,
    mut v_a_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Lean_Elab_toAttributeKind(v_attrKindStx_832_, v_a_833_, v_a_834_);
    crate::leanh::lean_dec_ref(v_a_833_);
    crate::leanh::lean_dec(v_attrKindStx_832_);
    return v_res_835_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__0(
    mut v_k_866_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: u8 = 0;
    v___x_867_ = l_Lean_Elab_elabAttr___redArg___lam__0___closed__1;
    v___x_868_ = lean_name_eq(v_k_866_, v___x_867_);
    if v___x_868_ == 0 {
        let mut v___x_869_: u8 = 0;
        v___x_869_ = 1;
        return v___x_869_;
    } else {
        let mut v___x_870_: u8 = 0;
        v___x_870_ = 0;
        return v___x_870_;
    }
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__0___boxed(
    mut v_k_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_872_: u8 = 0;
    let mut v_r_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_872_ = l_Lean_Elab_elabAttr___redArg___lam__0(v_k_871_);
    crate::leanh::lean_dec(v_k_871_);
    v_r_873_ = crate::leanh::lean_box((v_res_872_) as usize);
    return v_r_873_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__1(
    mut v_attrKind_874_: u8,
    mut v_attrName_875_: *mut crate::leanh::LeanObject,
    mut v_attr_876_: *mut crate::leanh::LeanObject,
    mut v_toPure_877_: *mut crate::leanh::LeanObject,
    mut v_____r_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_879_, 0, v_attrName_875_);
    crate::leanh::lean_ctor_set(v___x_879_, 1, v_attr_876_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_879_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v_attrKind_874_,
    );
    v___x_880_ = crate::leanh::lean_apply_2(v_toPure_877_, crate::leanh::lean_box(0), v___x_879_);
    return v___x_880_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__1___boxed(
    mut v_attrKind_881_: *mut crate::leanh::LeanObject,
    mut v_attrName_882_: *mut crate::leanh::LeanObject,
    mut v_attr_883_: *mut crate::leanh::LeanObject,
    mut v_toPure_884_: *mut crate::leanh::LeanObject,
    mut v_____r_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_886_: u8 = 0;
    let mut v_res_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_886_ = (crate::leanh::lean_unbox(v_attrKind_881_) as u8);
    v_res_887_ = l_Lean_Elab_elabAttr___redArg___lam__1(
        v_attrKind_boxed_886_,
        v_attrName_882_,
        v_attr_883_,
        v_toPure_884_,
        v_____r_885_,
    );
    return v_res_887_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__2(
    mut v___f_888_: *mut crate::leanh::LeanObject,
    mut v_____r_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = crate::leanh::lean_apply_1(v___f_888_, v_____r_889_);
    return v___x_890_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__3(
    mut v_inst_891_: *mut crate::leanh::LeanObject,
    mut v_inst_892_: *mut crate::leanh::LeanObject,
    mut v_inst_893_: *mut crate::leanh::LeanObject,
    mut v_inst_894_: *mut crate::leanh::LeanObject,
    mut v_inst_895_: *mut crate::leanh::LeanObject,
    mut v_inst_896_: *mut crate::leanh::LeanObject,
    mut v_ref_897_: *mut crate::leanh::LeanObject,
    mut v___x_898_: u8,
    mut v_toBind_899_: *mut crate::leanh::LeanObject,
    mut v___f_900_: *mut crate::leanh::LeanObject,
    mut v_____r_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMonadRef_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toMonadRef_902_ = crate::leanh::lean_ctor_get(v_inst_891_, 1);
    crate::leanh::lean_inc_ref(v_toMonadRef_902_);
    crate::leanh::lean_dec_ref(v_inst_891_);
    v___x_903_ = l_Lean_recordExtraModUseFromDecl___redArg(
        v_inst_892_,
        v_inst_893_,
        v_inst_894_,
        v_inst_895_,
        v_toMonadRef_902_,
        v_inst_896_,
        v_ref_897_,
        v___x_898_,
    );
    v___x_904_ = crate::leanh::lean_apply_4(
        v_toBind_899_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_903_,
        v___f_900_,
    );
    return v___x_904_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__3___boxed(
    mut v_inst_905_: *mut crate::leanh::LeanObject,
    mut v_inst_906_: *mut crate::leanh::LeanObject,
    mut v_inst_907_: *mut crate::leanh::LeanObject,
    mut v_inst_908_: *mut crate::leanh::LeanObject,
    mut v_inst_909_: *mut crate::leanh::LeanObject,
    mut v_inst_910_: *mut crate::leanh::LeanObject,
    mut v_ref_911_: *mut crate::leanh::LeanObject,
    mut v___x_912_: *mut crate::leanh::LeanObject,
    mut v_toBind_913_: *mut crate::leanh::LeanObject,
    mut v___f_914_: *mut crate::leanh::LeanObject,
    mut v_____r_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1457__boxed_916_: u8 = 0;
    let mut v_res_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457__boxed_916_ = (crate::leanh::lean_unbox(v___x_912_) as u8);
    v_res_917_ = l_Lean_Elab_elabAttr___redArg___lam__3(
        v_inst_905_,
        v_inst_906_,
        v_inst_907_,
        v_inst_908_,
        v_inst_909_,
        v_inst_910_,
        v_ref_911_,
        v___x_1457__boxed_916_,
        v_toBind_913_,
        v___f_914_,
        v_____r_915_,
    );
    return v_res_917_;
}
pub unsafe fn _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_919_ = l_Lean_Elab_elabAttr___redArg___lam__5___closed__0;
    v___x_920_ = l_Lean_stringToMessageData(v___x_919_);
    return v___x_920_;
}
pub unsafe fn _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_922_ = l_Lean_Elab_elabAttr___redArg___lam__5___closed__2;
    v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
    return v___x_923_;
}
pub unsafe fn _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lean_Elab_elabAttr___redArg___lam__5___closed__4;
    v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
    return v___x_926_;
}
pub unsafe fn _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_928_ = l_Lean_Elab_elabAttr___redArg___lam__5___closed__6;
    v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
    return v___x_929_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__5(
    mut v___f_930_: *mut crate::leanh::LeanObject,
    mut v_val_931_: *mut crate::leanh::LeanObject,
    mut v_attrName_932_: *mut crate::leanh::LeanObject,
    mut v_inst_933_: *mut crate::leanh::LeanObject,
    mut v_inst_934_: *mut crate::leanh::LeanObject,
    mut v_toBind_935_: *mut crate::leanh::LeanObject,
    mut v___f_936_: *mut crate::leanh::LeanObject,
    mut v_env_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: u8 = 0;
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasData_946_: u8 = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_941_ = l_Lean_Environment_header(v_env_937_);
                v_modules_942_ = crate::leanh::lean_ctor_get(v___x_941_, 3);
                crate::leanh::lean_inc_ref(v_modules_942_);
                crate::leanh::lean_dec_ref(v___x_941_);
                v___x_943_ = lean_array_get_size(v_modules_942_);
                v___x_944_ = lean_nat_dec_lt(v_val_931_, v___x_943_);
                if v___x_944_ == 0 {
                    crate::leanh::lean_dec_ref(v_modules_942_);
                    crate::leanh::lean_dec(v___f_936_);
                    crate::leanh::lean_dec(v_toBind_935_);
                    crate::leanh::lean_dec_ref(v_inst_934_);
                    crate::leanh::lean_dec_ref(v_inst_933_);
                    crate::leanh::lean_dec(v_attrName_932_);
                    state = 1;
                    continue;
                } else {
                    v___x_945_ = lean_array_fget_borrowed(v_modules_942_, v_val_931_);
                    v_hasData_946_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_945_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    if v_hasData_946_ == 0 {
                        crate::leanh::lean_dec(v___f_930_);
                        v___x_947_ = l_Lean_instInhabitedEffectiveImport_default;
                        v___x_948_ = lean_array_get(v___x_947_, v_modules_942_, v_val_931_);
                        crate::leanh::lean_dec_ref(v_modules_942_);
                        v_toImport_949_ = crate::leanh::lean_ctor_get(v___x_948_, 0);
                        crate::leanh::lean_inc_ref(v_toImport_949_);
                        crate::leanh::lean_dec(v___x_948_);
                        v_module_950_ = crate::leanh::lean_ctor_get(v_toImport_949_, 0);
                        crate::leanh::lean_inc(v_module_950_);
                        crate::leanh::lean_dec_ref(v_toImport_949_);
                        v___x_951_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__1_once
                            ),
                            _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__1,
                        );
                        v___x_952_ = l_Lean_MessageData_ofName(v_attrName_932_);
                        v___x_953_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_953_, 0, v___x_951_);
                        crate::leanh::lean_ctor_set(v___x_953_, 1, v___x_952_);
                        v___x_954_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__3_once
                            ),
                            _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__3,
                        );
                        v___x_955_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_955_, 0, v___x_953_);
                        crate::leanh::lean_ctor_set(v___x_955_, 1, v___x_954_);
                        v___x_956_ = l_Lean_MessageData_ofName(v_module_950_);
                        crate::leanh::lean_inc_ref(v___x_956_);
                        v___x_957_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_957_, 0, v___x_955_);
                        crate::leanh::lean_ctor_set(v___x_957_, 1, v___x_956_);
                        v___x_958_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__5_once
                            ),
                            _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__5,
                        );
                        v___x_959_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_959_, 0, v___x_957_);
                        crate::leanh::lean_ctor_set(v___x_959_, 1, v___x_958_);
                        v___x_960_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_960_, 0, v___x_959_);
                        crate::leanh::lean_ctor_set(v___x_960_, 1, v___x_956_);
                        v___x_961_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_elabAttr___redArg___lam__5___closed__7_once
                            ),
                            _init_l_Lean_Elab_elabAttr___redArg___lam__5___closed__7,
                        );
                        v___x_962_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_962_, 0, v___x_960_);
                        crate::leanh::lean_ctor_set(v___x_962_, 1, v___x_961_);
                        v___x_963_ =
                            l_Lean_throwError___redArg(v_inst_933_, v_inst_934_, v___x_962_);
                        v___x_964_ = crate::leanh::lean_apply_4(
                            v_toBind_935_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_963_,
                            v___f_936_,
                        );
                        return v___x_964_;
                    } else {
                        crate::leanh::lean_dec_ref(v_modules_942_);
                        crate::leanh::lean_dec(v___f_936_);
                        crate::leanh::lean_dec(v_toBind_935_);
                        crate::leanh::lean_dec_ref(v_inst_934_);
                        crate::leanh::lean_dec_ref(v_inst_933_);
                        crate::leanh::lean_dec(v_attrName_932_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_939_ = crate::leanh::lean_box(0);
                v___x_940_ = crate::leanh::lean_apply_1(v___f_930_, v___x_939_);
                return v___x_940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__5___boxed(
    mut v___f_965_: *mut crate::leanh::LeanObject,
    mut v_val_966_: *mut crate::leanh::LeanObject,
    mut v_attrName_967_: *mut crate::leanh::LeanObject,
    mut v_inst_968_: *mut crate::leanh::LeanObject,
    mut v_inst_969_: *mut crate::leanh::LeanObject,
    mut v_toBind_970_: *mut crate::leanh::LeanObject,
    mut v___f_971_: *mut crate::leanh::LeanObject,
    mut v_env_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_973_ = l_Lean_Elab_elabAttr___redArg___lam__5(
        v___f_965_,
        v_val_966_,
        v_attrName_967_,
        v_inst_968_,
        v_inst_969_,
        v_toBind_970_,
        v___f_971_,
        v_env_972_,
    );
    crate::leanh::lean_dec_ref(v_env_972_);
    crate::leanh::lean_dec(v_val_966_);
    return v_res_973_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__4(
    mut v_ref_974_: *mut crate::leanh::LeanObject,
    mut v___f_975_: *mut crate::leanh::LeanObject,
    mut v_attrName_976_: *mut crate::leanh::LeanObject,
    mut v_inst_977_: *mut crate::leanh::LeanObject,
    mut v_inst_978_: *mut crate::leanh::LeanObject,
    mut v_toBind_979_: *mut crate::leanh::LeanObject,
    mut v___f_980_: *mut crate::leanh::LeanObject,
    mut v_getEnv_981_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_982_, v_ref_974_);
    if crate::leanh::lean_obj_tag(v___x_983_) == 1 {
        let mut v_val_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_984_ = crate::leanh::lean_ctor_get(v___x_983_, 0);
        crate::leanh::lean_inc(v_val_984_);
        crate::leanh::lean_dec_ref_known(v___x_983_, 1);
        crate::leanh::lean_inc(v_toBind_979_);
        v___f_985_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_elabAttr___redArg___lam__5___boxed as *mut core::ffi::c_void,
            8,
            7,
        );
        crate::leanh::lean_closure_set(v___f_985_, 0, v___f_975_);
        crate::leanh::lean_closure_set(v___f_985_, 1, v_val_984_);
        crate::leanh::lean_closure_set(v___f_985_, 2, v_attrName_976_);
        crate::leanh::lean_closure_set(v___f_985_, 3, v_inst_977_);
        crate::leanh::lean_closure_set(v___f_985_, 4, v_inst_978_);
        crate::leanh::lean_closure_set(v___f_985_, 5, v_toBind_979_);
        crate::leanh::lean_closure_set(v___f_985_, 6, v___f_980_);
        v___x_986_ = crate::leanh::lean_apply_4(
            v_toBind_979_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_981_,
            v___f_985_,
        );
        return v___x_986_;
    } else {
        let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_983_);
        crate::leanh::lean_dec(v_getEnv_981_);
        crate::leanh::lean_dec(v___f_980_);
        crate::leanh::lean_dec(v_toBind_979_);
        crate::leanh::lean_dec_ref(v_inst_978_);
        crate::leanh::lean_dec_ref(v_inst_977_);
        crate::leanh::lean_dec(v_attrName_976_);
        v___x_987_ = crate::leanh::lean_box(0);
        v___x_988_ = crate::leanh::lean_apply_1(v___f_975_, v___x_987_);
        return v___x_988_;
    }
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__4___boxed(
    mut v_ref_989_: *mut crate::leanh::LeanObject,
    mut v___f_990_: *mut crate::leanh::LeanObject,
    mut v_attrName_991_: *mut crate::leanh::LeanObject,
    mut v_inst_992_: *mut crate::leanh::LeanObject,
    mut v_inst_993_: *mut crate::leanh::LeanObject,
    mut v_toBind_994_: *mut crate::leanh::LeanObject,
    mut v___f_995_: *mut crate::leanh::LeanObject,
    mut v_getEnv_996_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_998_ = l_Lean_Elab_elabAttr___redArg___lam__4(
        v_ref_989_,
        v___f_990_,
        v_attrName_991_,
        v_inst_992_,
        v_inst_993_,
        v_toBind_994_,
        v___f_995_,
        v_getEnv_996_,
        v_____do__lift_997_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_997_);
    crate::leanh::lean_dec(v_ref_989_);
    return v_res_998_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__6(
    mut v_a_999_: *mut crate::leanh::LeanObject,
    mut v___x_1000_: *mut crate::leanh::LeanObject,
    mut v___f_1001_: *mut crate::leanh::LeanObject,
    mut v_inst_1002_: *mut crate::leanh::LeanObject,
    mut v_inst_1003_: *mut crate::leanh::LeanObject,
    mut v_inst_1004_: *mut crate::leanh::LeanObject,
    mut v_inst_1005_: *mut crate::leanh::LeanObject,
    mut v_inst_1006_: *mut crate::leanh::LeanObject,
    mut v_inst_1007_: *mut crate::leanh::LeanObject,
    mut v_toBind_1008_: *mut crate::leanh::LeanObject,
    mut v___f_1009_: *mut crate::leanh::LeanObject,
    mut v_attrName_1010_: *mut crate::leanh::LeanObject,
    mut v_getEnv_1011_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toAttributeImplCore_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toAttributeImplCore_1013_ = crate::leanh::lean_ctor_get(v_a_999_, 0);
    crate::leanh::lean_inc_ref(v_toAttributeImplCore_1013_);
    crate::leanh::lean_dec_ref(v_a_999_);
    v_ref_1014_ = crate::leanh::lean_ctor_get(v_toAttributeImplCore_1013_, 0);
    crate::leanh::lean_inc_n(v_ref_1014_, 2);
    crate::leanh::lean_dec_ref(v_toAttributeImplCore_1013_);
    v___x_1015_ = l_Lean_regularInitAttr;
    v___x_1016_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_1000_,
        v___x_1015_,
        v_____do__lift_1012_,
        v_ref_1014_,
    );
    if crate::leanh::lean_obj_tag(v___x_1016_) == 0 {
        let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_ref_1014_);
        crate::leanh::lean_dec(v_getEnv_1011_);
        crate::leanh::lean_dec(v_attrName_1010_);
        crate::leanh::lean_dec(v___f_1009_);
        crate::leanh::lean_dec(v_toBind_1008_);
        crate::leanh::lean_dec(v_inst_1007_);
        crate::leanh::lean_dec(v_inst_1006_);
        crate::leanh::lean_dec_ref(v_inst_1005_);
        crate::leanh::lean_dec_ref(v_inst_1004_);
        crate::leanh::lean_dec_ref(v_inst_1003_);
        crate::leanh::lean_dec_ref(v_inst_1002_);
        v___x_1017_ = crate::leanh::lean_box(0);
        v___x_1018_ = crate::leanh::lean_apply_1(v___f_1001_, v___x_1017_);
        return v___x_1018_;
    } else {
        let mut v___x_1019_: u8 = 0;
        let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1016_, 1);
        crate::leanh::lean_dec(v___f_1001_);
        v___x_1019_ = 1;
        v___x_1020_ = crate::leanh::lean_box((v___x_1019_) as usize);
        crate::leanh::lean_inc_n(v_toBind_1008_, 2);
        crate::leanh::lean_inc(v_ref_1014_);
        crate::leanh::lean_inc_ref(v_inst_1003_);
        crate::leanh::lean_inc_ref(v_inst_1002_);
        v___f_1021_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_elabAttr___redArg___lam__3___boxed as *mut core::ffi::c_void,
            11,
            10,
        );
        crate::leanh::lean_closure_set(v___f_1021_, 0, v_inst_1002_);
        crate::leanh::lean_closure_set(v___f_1021_, 1, v_inst_1003_);
        crate::leanh::lean_closure_set(v___f_1021_, 2, v_inst_1004_);
        crate::leanh::lean_closure_set(v___f_1021_, 3, v_inst_1005_);
        crate::leanh::lean_closure_set(v___f_1021_, 4, v_inst_1006_);
        crate::leanh::lean_closure_set(v___f_1021_, 5, v_inst_1007_);
        crate::leanh::lean_closure_set(v___f_1021_, 6, v_ref_1014_);
        crate::leanh::lean_closure_set(v___f_1021_, 7, v___x_1020_);
        crate::leanh::lean_closure_set(v___f_1021_, 8, v_toBind_1008_);
        crate::leanh::lean_closure_set(v___f_1021_, 9, v___f_1009_);
        crate::leanh::lean_inc_ref(v___f_1021_);
        v___f_1022_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_elabAttr___redArg___lam__2 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1022_, 0, v___f_1021_);
        crate::leanh::lean_inc(v_getEnv_1011_);
        v___f_1023_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_elabAttr___redArg___lam__4___boxed as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_1023_, 0, v_ref_1014_);
        crate::leanh::lean_closure_set(v___f_1023_, 1, v___f_1021_);
        crate::leanh::lean_closure_set(v___f_1023_, 2, v_attrName_1010_);
        crate::leanh::lean_closure_set(v___f_1023_, 3, v_inst_1003_);
        crate::leanh::lean_closure_set(v___f_1023_, 4, v_inst_1002_);
        crate::leanh::lean_closure_set(v___f_1023_, 5, v_toBind_1008_);
        crate::leanh::lean_closure_set(v___f_1023_, 6, v___f_1022_);
        crate::leanh::lean_closure_set(v___f_1023_, 7, v_getEnv_1011_);
        v___x_1024_ = crate::leanh::lean_apply_4(
            v_toBind_1008_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1011_,
            v___f_1023_,
        );
        return v___x_1024_;
    }
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__7(
    mut v_attrName_1025_: *mut crate::leanh::LeanObject,
    mut v___x_1026_: *mut crate::leanh::LeanObject,
    mut v___f_1027_: *mut crate::leanh::LeanObject,
    mut v_inst_1028_: *mut crate::leanh::LeanObject,
    mut v_inst_1029_: *mut crate::leanh::LeanObject,
    mut v_inst_1030_: *mut crate::leanh::LeanObject,
    mut v_inst_1031_: *mut crate::leanh::LeanObject,
    mut v_inst_1032_: *mut crate::leanh::LeanObject,
    mut v_inst_1033_: *mut crate::leanh::LeanObject,
    mut v_toBind_1034_: *mut crate::leanh::LeanObject,
    mut v___f_1035_: *mut crate::leanh::LeanObject,
    mut v_getEnv_1036_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_attrName_1025_);
    v___x_1038_ = l_Lean_getAttributeImpl(v_____do__lift_1037_, v_attrName_1025_);
    if crate::leanh::lean_obj_tag(v___x_1038_) == 1 {
        let mut v_a_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1039_ = crate::leanh::lean_ctor_get(v___x_1038_, 0);
        crate::leanh::lean_inc(v_a_1039_);
        crate::leanh::lean_dec_ref_known(v___x_1038_, 1);
        crate::leanh::lean_inc(v_getEnv_1036_);
        crate::leanh::lean_inc(v_toBind_1034_);
        v___f_1040_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_elabAttr___redArg___lam__6 as *mut core::ffi::c_void,
            14,
            13,
        );
        crate::leanh::lean_closure_set(v___f_1040_, 0, v_a_1039_);
        crate::leanh::lean_closure_set(v___f_1040_, 1, v___x_1026_);
        crate::leanh::lean_closure_set(v___f_1040_, 2, v___f_1027_);
        crate::leanh::lean_closure_set(v___f_1040_, 3, v_inst_1028_);
        crate::leanh::lean_closure_set(v___f_1040_, 4, v_inst_1029_);
        crate::leanh::lean_closure_set(v___f_1040_, 5, v_inst_1030_);
        crate::leanh::lean_closure_set(v___f_1040_, 6, v_inst_1031_);
        crate::leanh::lean_closure_set(v___f_1040_, 7, v_inst_1032_);
        crate::leanh::lean_closure_set(v___f_1040_, 8, v_inst_1033_);
        crate::leanh::lean_closure_set(v___f_1040_, 9, v_toBind_1034_);
        crate::leanh::lean_closure_set(v___f_1040_, 10, v___f_1035_);
        crate::leanh::lean_closure_set(v___f_1040_, 11, v_attrName_1025_);
        crate::leanh::lean_closure_set(v___f_1040_, 12, v_getEnv_1036_);
        v___x_1041_ = crate::leanh::lean_apply_4(
            v_toBind_1034_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1036_,
            v___f_1040_,
        );
        return v___x_1041_;
    } else {
        let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1038_);
        crate::leanh::lean_dec(v_getEnv_1036_);
        crate::leanh::lean_dec(v___f_1035_);
        crate::leanh::lean_dec(v_toBind_1034_);
        crate::leanh::lean_dec(v_inst_1033_);
        crate::leanh::lean_dec(v_inst_1032_);
        crate::leanh::lean_dec_ref(v_inst_1031_);
        crate::leanh::lean_dec_ref(v_inst_1030_);
        crate::leanh::lean_dec_ref(v_inst_1029_);
        crate::leanh::lean_dec_ref(v_inst_1028_);
        crate::leanh::lean_dec(v___x_1026_);
        crate::leanh::lean_dec(v_attrName_1025_);
        v___x_1042_ = crate::leanh::lean_box(0);
        v___x_1043_ = crate::leanh::lean_apply_1(v___f_1027_, v___x_1042_);
        return v___x_1043_;
    }
}
pub unsafe fn _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Lean_Elab_elabAttr___redArg___lam__8___closed__0;
    v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
    return v___x_1046_;
}
pub unsafe fn _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = l_Lean_Elab_elabAttr___redArg___lam__8___closed__2;
    v___x_1049_ = l_Lean_stringToMessageData(v___x_1048_);
    return v___x_1049_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__8(
    mut v_attrName_1050_: *mut crate::leanh::LeanObject,
    mut v_toBind_1051_: *mut crate::leanh::LeanObject,
    mut v_getEnv_1052_: *mut crate::leanh::LeanObject,
    mut v___f_1053_: *mut crate::leanh::LeanObject,
    mut v_inst_1054_: *mut crate::leanh::LeanObject,
    mut v_inst_1055_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_attrName_1050_);
    v___x_1057_ = l_Lean_getAttributeImpl(v_____do__lift_1056_, v_attrName_1050_);
    if crate::leanh::lean_obj_tag(v___x_1057_) == 1 {
        let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1057_, 1);
        crate::leanh::lean_dec_ref(v_inst_1055_);
        crate::leanh::lean_dec_ref(v_inst_1054_);
        crate::leanh::lean_dec(v_attrName_1050_);
        v___x_1058_ = crate::leanh::lean_apply_4(
            v_toBind_1051_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_1052_,
            v___f_1053_,
        );
        return v___x_1058_;
    } else {
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1057_);
        crate::leanh::lean_dec(v___f_1053_);
        crate::leanh::lean_dec(v_getEnv_1052_);
        crate::leanh::lean_dec(v_toBind_1051_);
        v___x_1059_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_elabAttr___redArg___lam__8___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Elab_elabAttr___redArg___lam__8___closed__1_once),
            _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__1,
        );
        v___x_1060_ = l_Lean_MessageData_ofName(v_attrName_1050_);
        v___x_1061_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1061_, 0, v___x_1059_);
        crate::leanh::lean_ctor_set(v___x_1061_, 1, v___x_1060_);
        v___x_1062_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_elabAttr___redArg___lam__8___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Elab_elabAttr___redArg___lam__8___closed__3_once),
            _init_l_Lean_Elab_elabAttr___redArg___lam__8___closed__3,
        );
        v___x_1063_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1063_, 0, v___x_1061_);
        crate::leanh::lean_ctor_set(v___x_1063_, 1, v___x_1062_);
        v___x_1064_ = l_Lean_throwError___redArg(v_inst_1054_, v_inst_1055_, v___x_1063_);
        return v___x_1064_;
    }
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__9(
    mut v_inst_1065_: *mut crate::leanh::LeanObject,
    mut v_attrKind_1066_: u8,
    mut v_attr_1067_: *mut crate::leanh::LeanObject,
    mut v_toPure_1068_: *mut crate::leanh::LeanObject,
    mut v___x_1069_: *mut crate::leanh::LeanObject,
    mut v_inst_1070_: *mut crate::leanh::LeanObject,
    mut v_inst_1071_: *mut crate::leanh::LeanObject,
    mut v_inst_1072_: *mut crate::leanh::LeanObject,
    mut v_inst_1073_: *mut crate::leanh::LeanObject,
    mut v_inst_1074_: *mut crate::leanh::LeanObject,
    mut v_toBind_1075_: *mut crate::leanh::LeanObject,
    mut v_attrName_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getEnv_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getEnv_1077_ = crate::leanh::lean_ctor_get(v_inst_1065_, 0);
    crate::leanh::lean_inc_n(v_getEnv_1077_, 3);
    v___x_1078_ = crate::leanh::lean_box((v_attrKind_1066_) as usize);
    crate::leanh::lean_inc_n(v_attrName_1076_, 2);
    v___f_1079_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1079_, 0, v___x_1078_);
    crate::leanh::lean_closure_set(v___f_1079_, 1, v_attrName_1076_);
    crate::leanh::lean_closure_set(v___f_1079_, 2, v_attr_1067_);
    crate::leanh::lean_closure_set(v___f_1079_, 3, v_toPure_1068_);
    crate::leanh::lean_inc_ref(v___f_1079_);
    v___f_1080_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttr___redArg___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1080_, 0, v___f_1079_);
    crate::leanh::lean_inc_n(v_toBind_1075_, 2);
    crate::leanh::lean_inc_ref(v_inst_1071_);
    crate::leanh::lean_inc_ref(v_inst_1070_);
    v___f_1081_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttr___redArg___lam__7 as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_1081_, 0, v_attrName_1076_);
    crate::leanh::lean_closure_set(v___f_1081_, 1, v___x_1069_);
    crate::leanh::lean_closure_set(v___f_1081_, 2, v___f_1079_);
    crate::leanh::lean_closure_set(v___f_1081_, 3, v_inst_1070_);
    crate::leanh::lean_closure_set(v___f_1081_, 4, v_inst_1071_);
    crate::leanh::lean_closure_set(v___f_1081_, 5, v_inst_1065_);
    crate::leanh::lean_closure_set(v___f_1081_, 6, v_inst_1072_);
    crate::leanh::lean_closure_set(v___f_1081_, 7, v_inst_1073_);
    crate::leanh::lean_closure_set(v___f_1081_, 8, v_inst_1074_);
    crate::leanh::lean_closure_set(v___f_1081_, 9, v_toBind_1075_);
    crate::leanh::lean_closure_set(v___f_1081_, 10, v___f_1080_);
    crate::leanh::lean_closure_set(v___f_1081_, 11, v_getEnv_1077_);
    v___f_1082_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttr___redArg___lam__8 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1082_, 0, v_attrName_1076_);
    crate::leanh::lean_closure_set(v___f_1082_, 1, v_toBind_1075_);
    crate::leanh::lean_closure_set(v___f_1082_, 2, v_getEnv_1077_);
    crate::leanh::lean_closure_set(v___f_1082_, 3, v___f_1081_);
    crate::leanh::lean_closure_set(v___f_1082_, 4, v_inst_1071_);
    crate::leanh::lean_closure_set(v___f_1082_, 5, v_inst_1070_);
    v___x_1083_ = crate::leanh::lean_apply_4(
        v_toBind_1075_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1077_,
        v___f_1082_,
    );
    return v___x_1083_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__9___boxed(
    mut v_inst_1084_: *mut crate::leanh::LeanObject,
    mut v_attrKind_1085_: *mut crate::leanh::LeanObject,
    mut v_attr_1086_: *mut crate::leanh::LeanObject,
    mut v_toPure_1087_: *mut crate::leanh::LeanObject,
    mut v___x_1088_: *mut crate::leanh::LeanObject,
    mut v_inst_1089_: *mut crate::leanh::LeanObject,
    mut v_inst_1090_: *mut crate::leanh::LeanObject,
    mut v_inst_1091_: *mut crate::leanh::LeanObject,
    mut v_inst_1092_: *mut crate::leanh::LeanObject,
    mut v_inst_1093_: *mut crate::leanh::LeanObject,
    mut v_toBind_1094_: *mut crate::leanh::LeanObject,
    mut v_attrName_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_1096_: u8 = 0;
    let mut v_res_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_1096_ = (crate::leanh::lean_unbox(v_attrKind_1085_) as u8);
    v_res_1097_ = l_Lean_Elab_elabAttr___redArg___lam__9(
        v_inst_1084_,
        v_attrKind_boxed_1096_,
        v_attr_1086_,
        v_toPure_1087_,
        v___x_1088_,
        v_inst_1089_,
        v_inst_1090_,
        v_inst_1091_,
        v_inst_1092_,
        v_inst_1093_,
        v_toBind_1094_,
        v_attrName_1095_,
    );
    return v_res_1097_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__10(
    mut v___f_1098_: *mut crate::leanh::LeanObject,
    mut v_attrName_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1100_ = crate::leanh::lean_apply_1(v___f_1098_, v_attrName_1099_);
    return v___x_1100_;
}
pub unsafe fn _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = l_Lean_Elab_elabAttr___redArg___lam__13___closed__3;
    v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__13(
    mut v_inst_1111_: *mut crate::leanh::LeanObject,
    mut v_attrKind_1112_: u8,
    mut v_toPure_1113_: *mut crate::leanh::LeanObject,
    mut v___x_1114_: *mut crate::leanh::LeanObject,
    mut v_inst_1115_: *mut crate::leanh::LeanObject,
    mut v_inst_1116_: *mut crate::leanh::LeanObject,
    mut v_inst_1117_: *mut crate::leanh::LeanObject,
    mut v_inst_1118_: *mut crate::leanh::LeanObject,
    mut v_inst_1119_: *mut crate::leanh::LeanObject,
    mut v_toBind_1120_: *mut crate::leanh::LeanObject,
    mut v___x_1121_: *mut crate::leanh::LeanObject,
    mut v_attr_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    v___x_1123_ = crate::leanh::lean_box((v_attrKind_1112_) as usize);
    crate::leanh::lean_inc(v_toBind_1120_);
    crate::leanh::lean_inc_ref(v_inst_1116_);
    crate::leanh::lean_inc_ref(v_inst_1115_);
    crate::leanh::lean_inc(v_toPure_1113_);
    crate::leanh::lean_inc_n(v_attr_1122_, 2);
    v___f_1124_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttr___redArg___lam__9___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_1124_, 0, v_inst_1111_);
    crate::leanh::lean_closure_set(v___f_1124_, 1, v___x_1123_);
    crate::leanh::lean_closure_set(v___f_1124_, 2, v_attr_1122_);
    crate::leanh::lean_closure_set(v___f_1124_, 3, v_toPure_1113_);
    crate::leanh::lean_closure_set(v___f_1124_, 4, v___x_1114_);
    crate::leanh::lean_closure_set(v___f_1124_, 5, v_inst_1115_);
    crate::leanh::lean_closure_set(v___f_1124_, 6, v_inst_1116_);
    crate::leanh::lean_closure_set(v___f_1124_, 7, v_inst_1117_);
    crate::leanh::lean_closure_set(v___f_1124_, 8, v_inst_1118_);
    crate::leanh::lean_closure_set(v___f_1124_, 9, v_inst_1119_);
    crate::leanh::lean_closure_set(v___f_1124_, 10, v_toBind_1120_);
    v___x_1125_ = l_Lean_Syntax_getKind(v_attr_1122_);
    v___x_1126_ = l_Lean_Elab_elabAttr___redArg___lam__13___closed__2;
    v___x_1127_ = lean_name_eq(v___x_1125_, v___x_1126_);
    if v___x_1127_ == 0 {
        if crate::leanh::lean_obj_tag(v___x_1125_) == 1 {
            let mut v_str_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_attr_1122_);
            crate::leanh::lean_dec_ref(v_inst_1116_);
            crate::leanh::lean_dec_ref(v_inst_1115_);
            v_str_1128_ = crate::leanh::lean_ctor_get(v___x_1125_, 1);
            crate::leanh::lean_inc_ref(v_str_1128_);
            crate::leanh::lean_dec_ref_known(v___x_1125_, 2);
            v___f_1129_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_elabAttr___redArg___lam__10 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_1129_, 0, v___f_1124_);
            v___x_1130_ = crate::leanh::lean_box(0);
            v___x_1131_ = l_Lean_Name_str___override(v___x_1130_, v_str_1128_);
            v___x_1132_ =
                crate::leanh::lean_apply_2(v_toPure_1113_, crate::leanh::lean_box(0), v___x_1131_);
            v___x_1133_ = crate::leanh::lean_apply_4(
                v_toBind_1120_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1132_,
                v___f_1129_,
            );
            return v___x_1133_;
        } else {
            let mut v___f_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1125_);
            crate::leanh::lean_dec(v_toPure_1113_);
            v___f_1134_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_elabAttr___redArg___lam__10 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_1134_, 0, v___f_1124_);
            v___x_1135_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__4),
                core::ptr::addr_of_mut!(l_Lean_Elab_elabAttr___redArg___lam__13___closed__4_once),
                _init_l_Lean_Elab_elabAttr___redArg___lam__13___closed__4,
            );
            v___x_1136_ =
                l_Lean_throwErrorAt___redArg(v_inst_1116_, v_inst_1115_, v_attr_1122_, v___x_1135_);
            v___x_1137_ = crate::leanh::lean_apply_4(
                v_toBind_1120_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1136_,
                v___f_1134_,
            );
            return v___x_1137_;
        }
    } else {
        let mut v___f_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1125_);
        crate::leanh::lean_dec_ref(v_inst_1116_);
        crate::leanh::lean_dec_ref(v_inst_1115_);
        v___f_1138_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_elabAttr___redArg___lam__10 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1138_, 0, v___f_1124_);
        v___x_1139_ = l_Lean_Syntax_getArg(v_attr_1122_, v___x_1121_);
        crate::leanh::lean_dec(v_attr_1122_);
        v___x_1140_ = l_Lean_Syntax_getId(v___x_1139_);
        crate::leanh::lean_dec(v___x_1139_);
        v___x_1141_ = lean_erase_macro_scopes(v___x_1140_);
        v___x_1142_ =
            crate::leanh::lean_apply_2(v_toPure_1113_, crate::leanh::lean_box(0), v___x_1141_);
        v___x_1143_ = crate::leanh::lean_apply_4(
            v_toBind_1120_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1142_,
            v___f_1138_,
        );
        return v___x_1143_;
    }
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__13___boxed(
    mut v_inst_1144_: *mut crate::leanh::LeanObject,
    mut v_attrKind_1145_: *mut crate::leanh::LeanObject,
    mut v_toPure_1146_: *mut crate::leanh::LeanObject,
    mut v___x_1147_: *mut crate::leanh::LeanObject,
    mut v_inst_1148_: *mut crate::leanh::LeanObject,
    mut v_inst_1149_: *mut crate::leanh::LeanObject,
    mut v_inst_1150_: *mut crate::leanh::LeanObject,
    mut v_inst_1151_: *mut crate::leanh::LeanObject,
    mut v_inst_1152_: *mut crate::leanh::LeanObject,
    mut v_toBind_1153_: *mut crate::leanh::LeanObject,
    mut v___x_1154_: *mut crate::leanh::LeanObject,
    mut v_attr_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_1156_: u8 = 0;
    let mut v_res_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_1156_ = (crate::leanh::lean_unbox(v_attrKind_1145_) as u8);
    v_res_1157_ = l_Lean_Elab_elabAttr___redArg___lam__13(
        v_inst_1144_,
        v_attrKind_boxed_1156_,
        v_toPure_1146_,
        v___x_1147_,
        v_inst_1148_,
        v_inst_1149_,
        v_inst_1150_,
        v_inst_1151_,
        v_inst_1152_,
        v_toBind_1153_,
        v___x_1154_,
        v_attr_1155_,
    );
    crate::leanh::lean_dec(v___x_1154_);
    return v_res_1157_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__11(
    mut v_inst_1158_: *mut crate::leanh::LeanObject,
    mut v_toPure_1159_: *mut crate::leanh::LeanObject,
    mut v___x_1160_: *mut crate::leanh::LeanObject,
    mut v_inst_1161_: *mut crate::leanh::LeanObject,
    mut v_inst_1162_: *mut crate::leanh::LeanObject,
    mut v_inst_1163_: *mut crate::leanh::LeanObject,
    mut v_inst_1164_: *mut crate::leanh::LeanObject,
    mut v_inst_1165_: *mut crate::leanh::LeanObject,
    mut v_toBind_1166_: *mut crate::leanh::LeanObject,
    mut v___x_1167_: *mut crate::leanh::LeanObject,
    mut v_attrInstance_1168_: *mut crate::leanh::LeanObject,
    mut v___f_1169_: *mut crate::leanh::LeanObject,
    mut v_inst_1170_: *mut crate::leanh::LeanObject,
    mut v_inst_1171_: *mut crate::leanh::LeanObject,
    mut v_inst_1172_: *mut crate::leanh::LeanObject,
    mut v_attrKind_1173_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = crate::leanh::lean_box((v_attrKind_1173_) as usize);
    crate::leanh::lean_inc(v_toBind_1166_);
    crate::leanh::lean_inc(v_inst_1165_);
    crate::leanh::lean_inc(v_inst_1164_);
    crate::leanh::lean_inc_ref(v_inst_1163_);
    crate::leanh::lean_inc_ref(v_inst_1162_);
    crate::leanh::lean_inc_ref(v_inst_1161_);
    crate::leanh::lean_inc_ref(v_inst_1158_);
    v___f_1175_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttr___redArg___lam__13___boxed as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_1175_, 0, v_inst_1158_);
    crate::leanh::lean_closure_set(v___f_1175_, 1, v___x_1174_);
    crate::leanh::lean_closure_set(v___f_1175_, 2, v_toPure_1159_);
    crate::leanh::lean_closure_set(v___f_1175_, 3, v___x_1160_);
    crate::leanh::lean_closure_set(v___f_1175_, 4, v_inst_1161_);
    crate::leanh::lean_closure_set(v___f_1175_, 5, v_inst_1162_);
    crate::leanh::lean_closure_set(v___f_1175_, 6, v_inst_1163_);
    crate::leanh::lean_closure_set(v___f_1175_, 7, v_inst_1164_);
    crate::leanh::lean_closure_set(v___f_1175_, 8, v_inst_1165_);
    crate::leanh::lean_closure_set(v___f_1175_, 9, v_toBind_1166_);
    crate::leanh::lean_closure_set(v___f_1175_, 10, v___x_1167_);
    v___x_1176_ = crate::leanh::lean_unsigned_to_nat(1);
    v_attr_1177_ = l_Lean_Syntax_getArg(v_attrInstance_1168_, v___x_1176_);
    v___x_1178_ =
        crate::leanh::lean_alloc_closure(l_Lean_expandMacros as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1178_, 0, v_attr_1177_);
    crate::leanh::lean_closure_set(v___x_1178_, 1, v___f_1169_);
    v___x_1179_ = l_Lean_Elab_liftMacroM___redArg(
        v_inst_1162_,
        v_inst_1170_,
        v_inst_1158_,
        v_inst_1171_,
        v_inst_1161_,
        v_inst_1172_,
        v_inst_1163_,
        v_inst_1164_,
        v_inst_1165_,
        v___x_1178_,
    );
    v___x_1180_ = crate::leanh::lean_apply_4(
        v_toBind_1166_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1179_,
        v___f_1175_,
    );
    return v___x_1180_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg___lam__11___boxed(
    mut v_inst_1181_: *mut crate::leanh::LeanObject,
    mut v_toPure_1182_: *mut crate::leanh::LeanObject,
    mut v___x_1183_: *mut crate::leanh::LeanObject,
    mut v_inst_1184_: *mut crate::leanh::LeanObject,
    mut v_inst_1185_: *mut crate::leanh::LeanObject,
    mut v_inst_1186_: *mut crate::leanh::LeanObject,
    mut v_inst_1187_: *mut crate::leanh::LeanObject,
    mut v_inst_1188_: *mut crate::leanh::LeanObject,
    mut v_toBind_1189_: *mut crate::leanh::LeanObject,
    mut v___x_1190_: *mut crate::leanh::LeanObject,
    mut v_attrInstance_1191_: *mut crate::leanh::LeanObject,
    mut v___f_1192_: *mut crate::leanh::LeanObject,
    mut v_inst_1193_: *mut crate::leanh::LeanObject,
    mut v_inst_1194_: *mut crate::leanh::LeanObject,
    mut v_inst_1195_: *mut crate::leanh::LeanObject,
    mut v_attrKind_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_1197_: u8 = 0;
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_1197_ = (crate::leanh::lean_unbox(v_attrKind_1196_) as u8);
    v_res_1198_ = l_Lean_Elab_elabAttr___redArg___lam__11(
        v_inst_1181_,
        v_toPure_1182_,
        v___x_1183_,
        v_inst_1184_,
        v_inst_1185_,
        v_inst_1186_,
        v_inst_1187_,
        v_inst_1188_,
        v_toBind_1189_,
        v___x_1190_,
        v_attrInstance_1191_,
        v___f_1192_,
        v_inst_1193_,
        v_inst_1194_,
        v_inst_1195_,
        v_attrKind_boxed_1197_,
    );
    crate::leanh::lean_dec(v_attrInstance_1191_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Elab_elabAttr___redArg(
    mut v_inst_1200_: *mut crate::leanh::LeanObject,
    mut v_inst_1201_: *mut crate::leanh::LeanObject,
    mut v_inst_1202_: *mut crate::leanh::LeanObject,
    mut v_inst_1203_: *mut crate::leanh::LeanObject,
    mut v_inst_1204_: *mut crate::leanh::LeanObject,
    mut v_inst_1205_: *mut crate::leanh::LeanObject,
    mut v_inst_1206_: *mut crate::leanh::LeanObject,
    mut v_inst_1207_: *mut crate::leanh::LeanObject,
    mut v_inst_1208_: *mut crate::leanh::LeanObject,
    mut v_inst_1209_: *mut crate::leanh::LeanObject,
    mut v_attrInstance_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1211_ = crate::leanh::lean_ctor_get(v_inst_1200_, 0);
    v_toBind_1212_ = crate::leanh::lean_ctor_get(v_inst_1200_, 1);
    v_toPure_1213_ = crate::leanh::lean_ctor_get(v_toApplicative_1211_, 1);
    v___f_1214_ = l_Lean_Elab_elabAttr___redArg___closed__0;
    v___x_1215_ = crate::leanh::lean_box(0);
    v___x_1216_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1217_ = l_Lean_Syntax_getArg(v_attrInstance_1210_, v___x_1216_);
    v___x_1218_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_toAttributeKind___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1218_, 0, v___x_1217_);
    crate::leanh::lean_inc(v_inst_1208_);
    crate::leanh::lean_inc(v_inst_1207_);
    crate::leanh::lean_inc_ref(v_inst_1206_);
    crate::leanh::lean_inc_ref(v_inst_1202_);
    crate::leanh::lean_inc_ref(v_inst_1203_);
    crate::leanh::lean_inc_ref(v_inst_1205_);
    crate::leanh::lean_inc_ref_n(v_inst_1201_, 2);
    crate::leanh::lean_inc_ref(v_inst_1204_);
    crate::leanh::lean_inc_ref_n(v_inst_1200_, 2);
    v___x_1219_ = l_Lean_Elab_liftMacroM___redArg(
        v_inst_1200_,
        v_inst_1204_,
        v_inst_1201_,
        v_inst_1205_,
        v_inst_1203_,
        v_inst_1202_,
        v_inst_1206_,
        v_inst_1207_,
        v_inst_1208_,
        v___x_1218_,
    );
    crate::leanh::lean_inc_n(v_toBind_1212_, 2);
    crate::leanh::lean_inc(v_toPure_1213_);
    v___f_1220_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttr___redArg___lam__11___boxed as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_1220_, 0, v_inst_1201_);
    crate::leanh::lean_closure_set(v___f_1220_, 1, v_toPure_1213_);
    crate::leanh::lean_closure_set(v___f_1220_, 2, v___x_1215_);
    crate::leanh::lean_closure_set(v___f_1220_, 3, v_inst_1203_);
    crate::leanh::lean_closure_set(v___f_1220_, 4, v_inst_1200_);
    crate::leanh::lean_closure_set(v___f_1220_, 5, v_inst_1206_);
    crate::leanh::lean_closure_set(v___f_1220_, 6, v_inst_1207_);
    crate::leanh::lean_closure_set(v___f_1220_, 7, v_inst_1208_);
    crate::leanh::lean_closure_set(v___f_1220_, 8, v_toBind_1212_);
    crate::leanh::lean_closure_set(v___f_1220_, 9, v___x_1216_);
    crate::leanh::lean_closure_set(v___f_1220_, 10, v_attrInstance_1210_);
    crate::leanh::lean_closure_set(v___f_1220_, 11, v___f_1214_);
    crate::leanh::lean_closure_set(v___f_1220_, 12, v_inst_1204_);
    crate::leanh::lean_closure_set(v___f_1220_, 13, v_inst_1205_);
    crate::leanh::lean_closure_set(v___f_1220_, 14, v_inst_1202_);
    v___x_1221_ = crate::leanh::lean_apply_4(
        v_toBind_1212_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1219_,
        v___f_1220_,
    );
    v___x_1222_ = 1;
    v___x_1223_ = l_Lean_withoutExporting___redArg(
        v_inst_1200_,
        v_inst_1201_,
        v_inst_1209_,
        v___x_1221_,
        v___x_1222_,
    );
    return v___x_1223_;
}
pub unsafe fn l_Lean_Elab_elabAttr(
    mut v_m_1224_: *mut crate::leanh::LeanObject,
    mut v_inst_1225_: *mut crate::leanh::LeanObject,
    mut v_inst_1226_: *mut crate::leanh::LeanObject,
    mut v_inst_1227_: *mut crate::leanh::LeanObject,
    mut v_inst_1228_: *mut crate::leanh::LeanObject,
    mut v_inst_1229_: *mut crate::leanh::LeanObject,
    mut v_inst_1230_: *mut crate::leanh::LeanObject,
    mut v_inst_1231_: *mut crate::leanh::LeanObject,
    mut v_inst_1232_: *mut crate::leanh::LeanObject,
    mut v_inst_1233_: *mut crate::leanh::LeanObject,
    mut v_inst_1234_: *mut crate::leanh::LeanObject,
    mut v_inst_1235_: *mut crate::leanh::LeanObject,
    mut v_attrInstance_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_Elab_elabAttr___redArg(
        v_inst_1225_,
        v_inst_1226_,
        v_inst_1227_,
        v_inst_1228_,
        v_inst_1229_,
        v_inst_1230_,
        v_inst_1231_,
        v_inst_1232_,
        v_inst_1233_,
        v_inst_1235_,
        v_attrInstance_1236_,
    );
    return v___x_1237_;
}
pub unsafe fn l_Lean_Elab_elabAttr___boxed(
    mut v_m_1238_: *mut crate::leanh::LeanObject,
    mut v_inst_1239_: *mut crate::leanh::LeanObject,
    mut v_inst_1240_: *mut crate::leanh::LeanObject,
    mut v_inst_1241_: *mut crate::leanh::LeanObject,
    mut v_inst_1242_: *mut crate::leanh::LeanObject,
    mut v_inst_1243_: *mut crate::leanh::LeanObject,
    mut v_inst_1244_: *mut crate::leanh::LeanObject,
    mut v_inst_1245_: *mut crate::leanh::LeanObject,
    mut v_inst_1246_: *mut crate::leanh::LeanObject,
    mut v_inst_1247_: *mut crate::leanh::LeanObject,
    mut v_inst_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
    mut v_attrInstance_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Elab_elabAttr(
        v_m_1238_,
        v_inst_1239_,
        v_inst_1240_,
        v_inst_1241_,
        v_inst_1242_,
        v_inst_1243_,
        v_inst_1244_,
        v_inst_1245_,
        v_inst_1246_,
        v_inst_1247_,
        v_inst_1248_,
        v_inst_1249_,
        v_attrInstance_1250_,
    );
    crate::leanh::lean_dec(v_inst_1248_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__0(
    mut v_toPure_1252_: *mut crate::leanh::LeanObject,
    mut v_p_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_1254_ = crate::leanh::lean_ctor_get(v_p_1253_, 1);
    crate::leanh::lean_inc(v_snd_1254_);
    v___x_1255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1255_, 0, v_snd_1254_);
    v___x_1256_ =
        crate::leanh::lean_apply_2(v_toPure_1252_, crate::leanh::lean_box(0), v___x_1255_);
    return v___x_1256_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__0___boxed(
    mut v_toPure_1257_: *mut crate::leanh::LeanObject,
    mut v_p_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Lean_Elab_elabAttrs___redArg___lam__0(v_toPure_1257_, v_p_1258_);
    crate::leanh::lean_dec_ref(v_p_1258_);
    return v_res_1259_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__1(
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_withRef_1261_: *mut crate::leanh::LeanObject,
    mut v___x_1262_: *mut crate::leanh::LeanObject,
    mut v_oldRef_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1264_ = l_Lean_replaceRef(v_a_1260_, v_oldRef_1263_);
    v___x_1265_ = crate::leanh::lean_apply_3(
        v_withRef_1261_,
        crate::leanh::lean_box(0),
        v_ref_1264_,
        v___x_1262_,
    );
    return v___x_1265_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__1___boxed(
    mut v_a_1266_: *mut crate::leanh::LeanObject,
    mut v_withRef_1267_: *mut crate::leanh::LeanObject,
    mut v___x_1268_: *mut crate::leanh::LeanObject,
    mut v_oldRef_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_Elab_elabAttrs___redArg___lam__1(
        v_a_1266_,
        v_withRef_1267_,
        v___x_1268_,
        v_oldRef_1269_,
    );
    crate::leanh::lean_dec(v_oldRef_1269_);
    crate::leanh::lean_dec(v_a_1266_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__2(
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v_toPure_1272_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = lean_array_push(v___y_1271_, v_____do__lift_1273_);
    v___x_1275_ = crate::leanh::lean_box(0);
    v___x_1276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1276_, 0, v___x_1275_);
    crate::leanh::lean_ctor_set(v___x_1276_, 1, v___x_1274_);
    v___x_1277_ =
        crate::leanh::lean_apply_2(v_toPure_1272_, crate::leanh::lean_box(0), v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__3(
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v_toPure_1279_: *mut crate::leanh::LeanObject,
    mut v_____r_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1281_, 0, v_____r_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 1, v___y_1278_);
    v___x_1282_ =
        crate::leanh::lean_apply_2(v_toPure_1279_, crate::leanh::lean_box(0), v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__4(
    mut v_inst_1283_: *mut crate::leanh::LeanObject,
    mut v_inst_1284_: *mut crate::leanh::LeanObject,
    mut v_inst_1285_: *mut crate::leanh::LeanObject,
    mut v_inst_1286_: *mut crate::leanh::LeanObject,
    mut v_inst_1287_: *mut crate::leanh::LeanObject,
    mut v_toBind_1288_: *mut crate::leanh::LeanObject,
    mut v___f_1289_: *mut crate::leanh::LeanObject,
    mut v_ex_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Elab_logException___redArg(
        v_inst_1283_,
        v_inst_1284_,
        v_inst_1285_,
        v_inst_1286_,
        v_inst_1287_,
        v_ex_1290_,
    );
    v___x_1292_ = crate::leanh::lean_apply_4(
        v_toBind_1288_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1291_,
        v___f_1289_,
    );
    return v___x_1292_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__5(
    mut v_toMonadRef_1293_: *mut crate::leanh::LeanObject,
    mut v_toMonadExceptOf_1294_: *mut crate::leanh::LeanObject,
    mut v_inst_1295_: *mut crate::leanh::LeanObject,
    mut v_inst_1296_: *mut crate::leanh::LeanObject,
    mut v_inst_1297_: *mut crate::leanh::LeanObject,
    mut v_inst_1298_: *mut crate::leanh::LeanObject,
    mut v_inst_1299_: *mut crate::leanh::LeanObject,
    mut v_inst_1300_: *mut crate::leanh::LeanObject,
    mut v_inst_1301_: *mut crate::leanh::LeanObject,
    mut v_inst_1302_: *mut crate::leanh::LeanObject,
    mut v_inst_1303_: *mut crate::leanh::LeanObject,
    mut v_inst_1304_: *mut crate::leanh::LeanObject,
    mut v_toBind_1305_: *mut crate::leanh::LeanObject,
    mut v_toPure_1306_: *mut crate::leanh::LeanObject,
    mut v_inst_1307_: *mut crate::leanh::LeanObject,
    mut v_inst_1308_: *mut crate::leanh::LeanObject,
    mut v___f_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_x_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getRef_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_withRef_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getRef_1313_ = crate::leanh::lean_ctor_get(v_toMonadRef_1293_, 0);
    crate::leanh::lean_inc(v_getRef_1313_);
    v_withRef_1314_ = crate::leanh::lean_ctor_get(v_toMonadRef_1293_, 1);
    crate::leanh::lean_inc(v_withRef_1314_);
    crate::leanh::lean_dec_ref(v_toMonadRef_1293_);
    v_tryCatch_1315_ = crate::leanh::lean_ctor_get(v_toMonadExceptOf_1294_, 1);
    crate::leanh::lean_inc(v_tryCatch_1315_);
    crate::leanh::lean_dec_ref(v_toMonadExceptOf_1294_);
    crate::leanh::lean_inc(v_a_1310_);
    crate::leanh::lean_inc(v_inst_1303_);
    crate::leanh::lean_inc(v_inst_1302_);
    crate::leanh::lean_inc_ref(v_inst_1295_);
    v___x_1316_ = l_Lean_Elab_elabAttr___redArg(
        v_inst_1295_,
        v_inst_1296_,
        v_inst_1297_,
        v_inst_1298_,
        v_inst_1299_,
        v_inst_1300_,
        v_inst_1301_,
        v_inst_1302_,
        v_inst_1303_,
        v_inst_1304_,
        v_a_1310_,
    );
    v___f_1317_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttrs___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1317_, 0, v_a_1310_);
    crate::leanh::lean_closure_set(v___f_1317_, 1, v_withRef_1314_);
    crate::leanh::lean_closure_set(v___f_1317_, 2, v___x_1316_);
    crate::leanh::lean_inc_n(v_toBind_1305_, 3);
    v___x_1318_ = crate::leanh::lean_apply_4(
        v_toBind_1305_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRef_1313_,
        v___f_1317_,
    );
    crate::leanh::lean_inc(v_toPure_1306_);
    crate::leanh::lean_inc_ref(v___y_1312_);
    v___f_1319_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttrs___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1319_, 0, v___y_1312_);
    crate::leanh::lean_closure_set(v___f_1319_, 1, v_toPure_1306_);
    v___f_1320_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttrs___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1320_, 0, v___y_1312_);
    crate::leanh::lean_closure_set(v___f_1320_, 1, v_toPure_1306_);
    v___f_1321_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttrs___redArg___lam__4 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1321_, 0, v_inst_1295_);
    crate::leanh::lean_closure_set(v___f_1321_, 1, v_inst_1307_);
    crate::leanh::lean_closure_set(v___f_1321_, 2, v_inst_1303_);
    crate::leanh::lean_closure_set(v___f_1321_, 3, v_inst_1302_);
    crate::leanh::lean_closure_set(v___f_1321_, 4, v_inst_1308_);
    crate::leanh::lean_closure_set(v___f_1321_, 5, v_toBind_1305_);
    crate::leanh::lean_closure_set(v___f_1321_, 6, v___f_1320_);
    v___x_1322_ = crate::leanh::lean_apply_4(
        v_toBind_1305_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1318_,
        v___f_1319_,
    );
    v___x_1323_ = crate::leanh::lean_apply_3(
        v_tryCatch_1315_,
        crate::leanh::lean_box(0),
        v___x_1322_,
        v___f_1321_,
    );
    v___x_1324_ = crate::leanh::lean_apply_4(
        v_toBind_1305_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1323_,
        v___f_1309_,
    );
    return v___x_1324_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toMonadRef_1325_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_toMonadExceptOf_1326_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_1327_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_1328_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_1329_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_1330_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_inst_1331_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_inst_1332_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_1333_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_1334_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_1335_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_1336_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toBind_1337_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toPure_1338_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_1339_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_1340_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_1341_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_1342_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_x_1343_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_1344_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Lean_Elab_elabAttrs___redArg___lam__5(
        v_toMonadRef_1325_,
        v_toMonadExceptOf_1326_,
        v_inst_1327_,
        v_inst_1328_,
        v_inst_1329_,
        v_inst_1330_,
        v_inst_1331_,
        v_inst_1332_,
        v_inst_1333_,
        v_inst_1334_,
        v_inst_1335_,
        v_inst_1336_,
        v_toBind_1337_,
        v_toPure_1338_,
        v_inst_1339_,
        v_inst_1340_,
        v___f_1341_,
        v_a_1342_,
        v_x_1343_,
        v___y_1344_,
    );
    return v_res_1345_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg___lam__6(
    mut v_toPure_1346_: *mut crate::leanh::LeanObject,
    mut v_____s_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1348_ =
        crate::leanh::lean_apply_2(v_toPure_1346_, crate::leanh::lean_box(0), v_____s_1347_);
    return v___x_1348_;
}
pub unsafe fn l_Lean_Elab_elabAttrs___redArg(
    mut v_inst_1351_: *mut crate::leanh::LeanObject,
    mut v_inst_1352_: *mut crate::leanh::LeanObject,
    mut v_inst_1353_: *mut crate::leanh::LeanObject,
    mut v_inst_1354_: *mut crate::leanh::LeanObject,
    mut v_inst_1355_: *mut crate::leanh::LeanObject,
    mut v_inst_1356_: *mut crate::leanh::LeanObject,
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
    mut v_inst_1358_: *mut crate::leanh::LeanObject,
    mut v_inst_1359_: *mut crate::leanh::LeanObject,
    mut v_inst_1360_: *mut crate::leanh::LeanObject,
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
    mut v_inst_1362_: *mut crate::leanh::LeanObject,
    mut v_attrInstances_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadExceptOf_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1373_: usize = 0;
    let mut v___x_1374_: usize = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1364_ = crate::leanh::lean_ctor_get(v_inst_1351_, 0);
    v_toBind_1365_ = crate::leanh::lean_ctor_get(v_inst_1351_, 1);
    crate::leanh::lean_inc_n(v_toBind_1365_, 2);
    v_toMonadExceptOf_1366_ = crate::leanh::lean_ctor_get(v_inst_1354_, 0);
    crate::leanh::lean_inc_ref(v_toMonadExceptOf_1366_);
    v_toMonadRef_1367_ = crate::leanh::lean_ctor_get(v_inst_1354_, 1);
    crate::leanh::lean_inc_ref(v_toMonadRef_1367_);
    v_toPure_1368_ = crate::leanh::lean_ctor_get(v_toApplicative_1364_, 1);
    v_attrs_1369_ = l_Lean_Elab_elabAttrs___redArg___closed__0;
    crate::leanh::lean_inc_n(v_toPure_1368_, 3);
    v___f_1370_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttrs___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1370_, 0, v_toPure_1368_);
    crate::leanh::lean_inc_ref(v_inst_1351_);
    v___f_1371_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttrs___redArg___lam__5___boxed as *mut core::ffi::c_void,
        20,
        17,
    );
    crate::leanh::lean_closure_set(v___f_1371_, 0, v_toMonadRef_1367_);
    crate::leanh::lean_closure_set(v___f_1371_, 1, v_toMonadExceptOf_1366_);
    crate::leanh::lean_closure_set(v___f_1371_, 2, v_inst_1351_);
    crate::leanh::lean_closure_set(v___f_1371_, 3, v_inst_1352_);
    crate::leanh::lean_closure_set(v___f_1371_, 4, v_inst_1353_);
    crate::leanh::lean_closure_set(v___f_1371_, 5, v_inst_1354_);
    crate::leanh::lean_closure_set(v___f_1371_, 6, v_inst_1355_);
    crate::leanh::lean_closure_set(v___f_1371_, 7, v_inst_1356_);
    crate::leanh::lean_closure_set(v___f_1371_, 8, v_inst_1357_);
    crate::leanh::lean_closure_set(v___f_1371_, 9, v_inst_1358_);
    crate::leanh::lean_closure_set(v___f_1371_, 10, v_inst_1359_);
    crate::leanh::lean_closure_set(v___f_1371_, 11, v_inst_1362_);
    crate::leanh::lean_closure_set(v___f_1371_, 12, v_toBind_1365_);
    crate::leanh::lean_closure_set(v___f_1371_, 13, v_toPure_1368_);
    crate::leanh::lean_closure_set(v___f_1371_, 14, v_inst_1360_);
    crate::leanh::lean_closure_set(v___f_1371_, 15, v_inst_1361_);
    crate::leanh::lean_closure_set(v___f_1371_, 16, v___f_1370_);
    v___f_1372_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_elabAttrs___redArg___lam__6 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1372_, 0, v_toPure_1368_);
    v_sz_1373_ = lean_array_size(v_attrInstances_1363_);
    v___x_1374_ = 0usize;
    v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1351_,
        v_attrInstances_1363_,
        v___f_1371_,
        v_sz_1373_,
        v___x_1374_,
        v_attrs_1369_,
    );
    v___x_1376_ = crate::leanh::lean_apply_4(
        v_toBind_1365_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1375_,
        v___f_1372_,
    );
    return v___x_1376_;
}
pub unsafe fn l_Lean_Elab_elabAttrs(
    mut v_m_1377_: *mut crate::leanh::LeanObject,
    mut v_inst_1378_: *mut crate::leanh::LeanObject,
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
    mut v_inst_1380_: *mut crate::leanh::LeanObject,
    mut v_inst_1381_: *mut crate::leanh::LeanObject,
    mut v_inst_1382_: *mut crate::leanh::LeanObject,
    mut v_inst_1383_: *mut crate::leanh::LeanObject,
    mut v_inst_1384_: *mut crate::leanh::LeanObject,
    mut v_inst_1385_: *mut crate::leanh::LeanObject,
    mut v_inst_1386_: *mut crate::leanh::LeanObject,
    mut v_inst_1387_: *mut crate::leanh::LeanObject,
    mut v_inst_1388_: *mut crate::leanh::LeanObject,
    mut v_inst_1389_: *mut crate::leanh::LeanObject,
    mut v_attrInstances_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = l_Lean_Elab_elabAttrs___redArg(
        v_inst_1378_,
        v_inst_1379_,
        v_inst_1380_,
        v_inst_1381_,
        v_inst_1382_,
        v_inst_1383_,
        v_inst_1384_,
        v_inst_1385_,
        v_inst_1386_,
        v_inst_1387_,
        v_inst_1388_,
        v_inst_1389_,
        v_attrInstances_1390_,
    );
    return v___x_1391_;
}
pub unsafe fn l_Lean_Elab_elabDeclAttrs___redArg(
    mut v_inst_1392_: *mut crate::leanh::LeanObject,
    mut v_inst_1393_: *mut crate::leanh::LeanObject,
    mut v_inst_1394_: *mut crate::leanh::LeanObject,
    mut v_inst_1395_: *mut crate::leanh::LeanObject,
    mut v_inst_1396_: *mut crate::leanh::LeanObject,
    mut v_inst_1397_: *mut crate::leanh::LeanObject,
    mut v_inst_1398_: *mut crate::leanh::LeanObject,
    mut v_inst_1399_: *mut crate::leanh::LeanObject,
    mut v_inst_1400_: *mut crate::leanh::LeanObject,
    mut v_inst_1401_: *mut crate::leanh::LeanObject,
    mut v_inst_1402_: *mut crate::leanh::LeanObject,
    mut v_inst_1403_: *mut crate::leanh::LeanObject,
    mut v_stx_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1406_ = l_Lean_Syntax_getArg(v_stx_1404_, v___x_1405_);
    v___x_1407_ = l_Lean_Syntax_getSepArgs(v___x_1406_);
    crate::leanh::lean_dec(v___x_1406_);
    v___x_1408_ = l_Lean_Elab_elabAttrs___redArg(
        v_inst_1392_,
        v_inst_1393_,
        v_inst_1394_,
        v_inst_1395_,
        v_inst_1396_,
        v_inst_1397_,
        v_inst_1398_,
        v_inst_1399_,
        v_inst_1400_,
        v_inst_1401_,
        v_inst_1402_,
        v_inst_1403_,
        v___x_1407_,
    );
    return v___x_1408_;
}
pub unsafe fn l_Lean_Elab_elabDeclAttrs___redArg___boxed(
    mut v_inst_1409_: *mut crate::leanh::LeanObject,
    mut v_inst_1410_: *mut crate::leanh::LeanObject,
    mut v_inst_1411_: *mut crate::leanh::LeanObject,
    mut v_inst_1412_: *mut crate::leanh::LeanObject,
    mut v_inst_1413_: *mut crate::leanh::LeanObject,
    mut v_inst_1414_: *mut crate::leanh::LeanObject,
    mut v_inst_1415_: *mut crate::leanh::LeanObject,
    mut v_inst_1416_: *mut crate::leanh::LeanObject,
    mut v_inst_1417_: *mut crate::leanh::LeanObject,
    mut v_inst_1418_: *mut crate::leanh::LeanObject,
    mut v_inst_1419_: *mut crate::leanh::LeanObject,
    mut v_inst_1420_: *mut crate::leanh::LeanObject,
    mut v_stx_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Lean_Elab_elabDeclAttrs___redArg(
        v_inst_1409_,
        v_inst_1410_,
        v_inst_1411_,
        v_inst_1412_,
        v_inst_1413_,
        v_inst_1414_,
        v_inst_1415_,
        v_inst_1416_,
        v_inst_1417_,
        v_inst_1418_,
        v_inst_1419_,
        v_inst_1420_,
        v_stx_1421_,
    );
    crate::leanh::lean_dec(v_stx_1421_);
    return v_res_1422_;
}
pub unsafe fn l_Lean_Elab_elabDeclAttrs(
    mut v_m_1423_: *mut crate::leanh::LeanObject,
    mut v_inst_1424_: *mut crate::leanh::LeanObject,
    mut v_inst_1425_: *mut crate::leanh::LeanObject,
    mut v_inst_1426_: *mut crate::leanh::LeanObject,
    mut v_inst_1427_: *mut crate::leanh::LeanObject,
    mut v_inst_1428_: *mut crate::leanh::LeanObject,
    mut v_inst_1429_: *mut crate::leanh::LeanObject,
    mut v_inst_1430_: *mut crate::leanh::LeanObject,
    mut v_inst_1431_: *mut crate::leanh::LeanObject,
    mut v_inst_1432_: *mut crate::leanh::LeanObject,
    mut v_inst_1433_: *mut crate::leanh::LeanObject,
    mut v_inst_1434_: *mut crate::leanh::LeanObject,
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_stx_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = l_Lean_Elab_elabDeclAttrs___redArg(
        v_inst_1424_,
        v_inst_1425_,
        v_inst_1426_,
        v_inst_1427_,
        v_inst_1428_,
        v_inst_1429_,
        v_inst_1430_,
        v_inst_1431_,
        v_inst_1432_,
        v_inst_1433_,
        v_inst_1434_,
        v_inst_1435_,
        v_stx_1436_,
    );
    return v___x_1437_;
}
pub unsafe fn l_Lean_Elab_elabDeclAttrs___boxed(
    mut v_m_1438_: *mut crate::leanh::LeanObject,
    mut v_inst_1439_: *mut crate::leanh::LeanObject,
    mut v_inst_1440_: *mut crate::leanh::LeanObject,
    mut v_inst_1441_: *mut crate::leanh::LeanObject,
    mut v_inst_1442_: *mut crate::leanh::LeanObject,
    mut v_inst_1443_: *mut crate::leanh::LeanObject,
    mut v_inst_1444_: *mut crate::leanh::LeanObject,
    mut v_inst_1445_: *mut crate::leanh::LeanObject,
    mut v_inst_1446_: *mut crate::leanh::LeanObject,
    mut v_inst_1447_: *mut crate::leanh::LeanObject,
    mut v_inst_1448_: *mut crate::leanh::LeanObject,
    mut v_inst_1449_: *mut crate::leanh::LeanObject,
    mut v_inst_1450_: *mut crate::leanh::LeanObject,
    mut v_stx_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_Lean_Elab_elabDeclAttrs(
        v_m_1438_,
        v_inst_1439_,
        v_inst_1440_,
        v_inst_1441_,
        v_inst_1442_,
        v_inst_1443_,
        v_inst_1444_,
        v_inst_1445_,
        v_inst_1446_,
        v_inst_1447_,
        v_inst_1448_,
        v_inst_1449_,
        v_inst_1450_,
        v_stx_1451_,
    );
    crate::leanh::lean_dec(v_stx_1451_);
    return v_res_1452_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Attributes(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Attributes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Attributes(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Attributes(builtin);
}
