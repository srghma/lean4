// Lean compiler output
// Module: Lean.Declaration
// Imports: Lean.Expr Init.Data.Ord.UInt Init.Data.ToString.Macro
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Control::l_List_foldlM___redArg;
use crate::r#gen::Init::Data::Ord::UInt::{
    initialize_Init_Data_Ord_UInt, runtime_initialize_Init_Data_Ord_UInt,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_appendCore, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_str___override,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_bindingBody_x21, l_Lean_Expr_bindingDomain_x21,
    l_Lean_Expr_const___override, l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn,
    l_Lean_instInhabitedExpr, runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_uint32_dec_eq, lean_uint32_dec_lt,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static mut l_Lean_instInhabitedReducibilityHints_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedReducibilityHints: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqReducibilityHints___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqReducibilityHints_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqReducibilityHints___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqReducibilityHints___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqReducibilityHints: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqReducibilityHints___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ReducibilityHints_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_ReducibilityHints_compare___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ReducibilityHints_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityHints_instOrd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_ReducibilityHints_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityHints_instOrd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedConstantVal_default___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_instInhabitedConstantVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedConstantVal_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instInhabitedConstantVal_default___closed__1_value: crate::leanh::LeanCtorObject<
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instInhabitedConstantVal_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedConstantVal_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedConstantVal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedConstantVal_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedConstantVal_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedConstantVal_default___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedConstantVal_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstantVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstantVal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqConstantVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqConstantVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqConstantVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqConstantVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqConstantVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqConstantVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedAxiomVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedAxiomVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedAxiomVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedAxiomVal: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instBEqAxiomVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqAxiomVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqAxiomVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqAxiomVal___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqAxiomVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqAxiomVal___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedDefinitionSafety_default: u8 = 0;
pub static mut l_Lean_instInhabitedDefinitionSafety: u8 = 0;
pub static l_Lean_instBEqDefinitionSafety___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqDefinitionSafety_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqDefinitionSafety___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDefinitionSafety___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqDefinitionSafety: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDefinitionSafety___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDefinitionSafety_repr___closed__0_value: crate::leanh::LeanStringObject<
    29,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 83, 97, 102, 101,
        116, 121, 46, 117, 110, 115, 97, 102, 101, 0,
    ],
};
static mut l_Lean_instReprDefinitionSafety_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDefinitionSafety_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDefinitionSafety_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDefinitionSafety_repr___closed__2_value: crate::leanh::LeanStringObject<
    27,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 83, 97, 102, 101,
        116, 121, 46, 115, 97, 102, 101, 0,
    ],
};
static mut l_Lean_instReprDefinitionSafety_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDefinitionSafety_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDefinitionSafety_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDefinitionSafety_repr___closed__4_value: crate::leanh::LeanStringObject<
    30,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        76, 101, 97, 110, 46, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 83, 97, 102, 101,
        116, 121, 46, 112, 97, 114, 116, 105, 97, 108, 0,
    ],
};
static mut l_Lean_instReprDefinitionSafety_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprDefinitionSafety_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDefinitionSafety_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprDefinitionSafety_repr___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDefinitionSafety_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprDefinitionSafety_repr___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDefinitionSafety_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDefinitionSafety___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprDefinitionSafety_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprDefinitionSafety___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprDefinitionSafety: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDefinitionSafety___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedDefinitionVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedDefinitionVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instInhabitedDefinitionVal_default___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedDefinitionVal_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDefinitionVal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedDefinitionVal_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedDefinitionVal_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDefinitionVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDefinitionVal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqDefinitionVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqDefinitionVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqDefinitionVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDefinitionVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqDefinitionVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDefinitionVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedTheoremVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedTheoremVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTheoremVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedTheoremVal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqTheoremVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqTheoremVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqTheoremVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqTheoremVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqTheoremVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqTheoremVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedOpaqueVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedOpaqueVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedOpaqueVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedOpaqueVal: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instBEqOpaqueVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqOpaqueVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqOpaqueVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqOpaqueVal___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqOpaqueVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqOpaqueVal___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedConstructor_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedConstructor_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedConstructor_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedConstructor_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstructor_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstructor: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqConstructor___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqConstructor_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqConstructor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqConstructor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqConstructor: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqConstructor___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedInductiveType_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedInductiveType_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedInductiveType_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedInductiveType: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqInductiveType___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqInductiveType_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqInductiveType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqInductiveType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqInductiveType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqInductiveType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedDeclaration_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedDeclaration_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclaration_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedDeclaration: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqDeclaration___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqDeclaration_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqDeclaration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDeclaration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqDeclaration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDeclaration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_definitionVal_x21___closed__0_value: crate::leanh::LeanStringObject<
    17,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        76, 101, 97, 110, 46, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Declaration_definitionVal_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_definitionVal_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_definitionVal_x21___closed__1_value: crate::leanh::LeanStringObject<
    32,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        76, 101, 97, 110, 46, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 46, 100, 101, 102,
        105, 110, 105, 116, 105, 111, 110, 86, 97, 108, 33, 0,
    ],
};
static mut l_Lean_Declaration_definitionVal_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_definitionVal_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_definitionVal_x21___closed__2_value: crate::leanh::LeanStringObject<
    35,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 68, 101, 99, 108, 97, 114, 97, 116,
        105, 111, 110, 46, 100, 101, 102, 110, 68, 101, 99, 108, 96, 46, 0,
    ],
};
static mut l_Lean_Declaration_definitionVal_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_definitionVal_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Declaration_definitionVal_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Declaration_definitionVal_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Declaration_getTopLevelNames___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [81, 117, 111, 116, 0],
};
static mut l_Lean_Declaration_getTopLevelNames___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getTopLevelNames___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14456664134214385499 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getTopLevelNames___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getTopLevelNames___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getTopLevelNames___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 99, 0]};
static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,15905184149013948946 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Declaration_getNames___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Declaration_getNames___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14456664134214385499 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Declaration_getNames___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17886754359162270207 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getNames___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 105, 102, 116, 0],
    };
static mut l_Lean_Declaration_getNames___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Declaration_getNames___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14456664134214385499 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Declaration_getNames___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__2_value)
                as *mut crate::leanh::LeanObject,
            5821404849734319451 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getNames___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__4_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 110, 100, 0],
    };
static mut l_Lean_Declaration_getNames___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Declaration_getNames___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14456664134214385499 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Declaration_getNames___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__4_value)
                as *mut crate::leanh::LeanObject,
            4362047871608542614 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getNames___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getNames___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getNames___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getNames___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Declaration_getTopLevelNames___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Declaration_getNames___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Declaration_getNames___closed__10_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Declaration_getNames___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Declaration_getNames___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedInductiveVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedInductiveVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedInductiveVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedInductiveVal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedConstructorVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedConstructorVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstructorVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstructorVal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqConstructorVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqConstructorVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqConstructorVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqConstructorVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqConstructorVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqConstructorVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedRecursorRule_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedRecursorRule_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedRecursorRule_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedRecursorRule: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqRecursorRule___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqRecursorRule_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqRecursorRule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqRecursorRule___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqRecursorRule: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqRecursorRule___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instInhabitedRecursorVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedRecursorVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedRecursorVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedRecursorVal: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqRecursorVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqRecursorVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqRecursorVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqRecursorVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqRecursorVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqRecursorVal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedQuotKind_default: u8 = 0;
pub static mut l_Lean_instInhabitedQuotKind: u8 = 0;
static mut l_Lean_instInhabitedQuotVal_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedQuotVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedQuotVal_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedQuotVal: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedConstantInfo_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedConstantInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstantInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedConstantInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ConstantInfo_value_x21___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 110, 115, 116, 97, 110, 116, 73, 110, 102, 111, 46, 118,
            97, 108, 117, 101, 33, 0,
        ],
    };
static mut l_Lean_ConstantInfo_value_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ConstantInfo_value_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ConstantInfo_value_x21___closed__1_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 118,
            97, 108, 117, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_ConstantInfo_value_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ConstantInfo_value_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ConstantInfo_value_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ConstantInfo_value_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ConstantInfo_value_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ConstantInfo_value_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ConstantInfo_value_x21___closed__4_value: crate::leanh::LeanStringObject<38> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 118,
            97, 108, 117, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 44, 32, 98, 117, 116, 32,
            0,
        ],
    };
static mut l_Lean_ConstantInfo_value_x21___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ConstantInfo_value_x21___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ConstantInfo_value_x21___closed__5_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [32, 104, 97, 115, 32, 110, 111, 110, 101, 0],
    };
static mut l_Lean_ConstantInfo_value_x21___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ConstantInfo_value_x21___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ConstantInfo_inductiveVal_x21___closed__0_value: crate::leanh::LeanStringObject<
    32,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 110, 115, 116, 97, 110, 116, 73, 110, 102, 111, 46, 105,
        110, 100, 117, 99, 116, 105, 118, 101, 86, 97, 108, 33, 0,
    ],
};
static mut l_Lean_ConstantInfo_inductiveVal_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ConstantInfo_inductiveVal_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ConstantInfo_inductiveVal_x21___closed__1_value: crate::leanh::LeanStringObject<
    38,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 67, 111, 110, 115, 116, 97, 110, 116,
        73, 110, 102, 111, 46, 105, 110, 100, 117, 99, 116, 73, 110, 102, 111, 96, 46, 0,
    ],
};
static mut l_Lean_ConstantInfo_inductiveVal_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ConstantInfo_inductiveVal_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ConstantInfo_inductiveVal_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_ReducibilityHints_ctorIdx(
    mut v_x_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1680_) {
        0 => {
            let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1681_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1681_;
        }
        1 => {
            let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1682_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1682_;
        }
        _ => {
            let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1683_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1683_;
        }
    }
}
pub unsafe fn l_Lean_ReducibilityHints_ctorIdx___boxed(
    mut v_x_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1685_ = l_Lean_ReducibilityHints_ctorIdx(v_x_1684_);
    crate::leanh::lean_dec(v_x_1684_);
    return v_res_1685_;
}
pub unsafe fn l_Lean_ReducibilityHints_ctorElim___redArg(
    mut v_t_1686_: *mut crate::leanh::LeanObject,
    mut v_k_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1686_) == 2 {
        let mut v_a_1688_: u32 = 0;
        let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1688_ = crate::leanh::lean_ctor_get_uint32(v_t_1686_, 0 as u32);
        v___x_1689_ = crate::leanh::lean_box_uint32(v_a_1688_);
        v___x_1690_ = crate::leanh::lean_apply_1(v_k_1687_, v___x_1689_);
        return v___x_1690_;
    } else {
        return v_k_1687_;
    }
}
pub unsafe fn l_Lean_ReducibilityHints_ctorElim___redArg___boxed(
    mut v_t_1691_: *mut crate::leanh::LeanObject,
    mut v_k_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1691_, v_k_1692_);
    crate::leanh::lean_dec(v_t_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_ReducibilityHints_ctorElim(
    mut v_motive_1694_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1695_: *mut crate::leanh::LeanObject,
    mut v_t_1696_: *mut crate::leanh::LeanObject,
    mut v_h_1697_: *mut crate::leanh::LeanObject,
    mut v_k_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1696_, v_k_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Lean_ReducibilityHints_ctorElim___boxed(
    mut v_motive_1700_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1701_: *mut crate::leanh::LeanObject,
    mut v_t_1702_: *mut crate::leanh::LeanObject,
    mut v_h_1703_: *mut crate::leanh::LeanObject,
    mut v_k_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1705_ = l_Lean_ReducibilityHints_ctorElim(
        v_motive_1700_,
        v_ctorIdx_1701_,
        v_t_1702_,
        v_h_1703_,
        v_k_1704_,
    );
    crate::leanh::lean_dec(v_t_1702_);
    crate::leanh::lean_dec(v_ctorIdx_1701_);
    return v_res_1705_;
}
pub unsafe fn l_Lean_ReducibilityHints_opaque_elim___redArg(
    mut v_t_1706_: *mut crate::leanh::LeanObject,
    mut v_opaque_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1708_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1706_, v_opaque_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_ReducibilityHints_opaque_elim___redArg___boxed(
    mut v_t_1709_: *mut crate::leanh::LeanObject,
    mut v_opaque_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1711_ = l_Lean_ReducibilityHints_opaque_elim___redArg(v_t_1709_, v_opaque_1710_);
    crate::leanh::lean_dec(v_t_1709_);
    return v_res_1711_;
}
pub unsafe fn l_Lean_ReducibilityHints_opaque_elim(
    mut v_motive_1712_: *mut crate::leanh::LeanObject,
    mut v_t_1713_: *mut crate::leanh::LeanObject,
    mut v_h_1714_: *mut crate::leanh::LeanObject,
    mut v_opaque_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1713_, v_opaque_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Lean_ReducibilityHints_opaque_elim___boxed(
    mut v_motive_1717_: *mut crate::leanh::LeanObject,
    mut v_t_1718_: *mut crate::leanh::LeanObject,
    mut v_h_1719_: *mut crate::leanh::LeanObject,
    mut v_opaque_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ =
        l_Lean_ReducibilityHints_opaque_elim(v_motive_1717_, v_t_1718_, v_h_1719_, v_opaque_1720_);
    crate::leanh::lean_dec(v_t_1718_);
    return v_res_1721_;
}
pub unsafe fn l_Lean_ReducibilityHints_abbrev_elim___redArg(
    mut v_t_1722_: *mut crate::leanh::LeanObject,
    mut v_abbrev_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1722_, v_abbrev_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_ReducibilityHints_abbrev_elim___redArg___boxed(
    mut v_t_1725_: *mut crate::leanh::LeanObject,
    mut v_abbrev_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1727_ = l_Lean_ReducibilityHints_abbrev_elim___redArg(v_t_1725_, v_abbrev_1726_);
    crate::leanh::lean_dec(v_t_1725_);
    return v_res_1727_;
}
pub unsafe fn l_Lean_ReducibilityHints_abbrev_elim(
    mut v_motive_1728_: *mut crate::leanh::LeanObject,
    mut v_t_1729_: *mut crate::leanh::LeanObject,
    mut v_h_1730_: *mut crate::leanh::LeanObject,
    mut v_abbrev_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1729_, v_abbrev_1731_);
    return v___x_1732_;
}
pub unsafe fn l_Lean_ReducibilityHints_abbrev_elim___boxed(
    mut v_motive_1733_: *mut crate::leanh::LeanObject,
    mut v_t_1734_: *mut crate::leanh::LeanObject,
    mut v_h_1735_: *mut crate::leanh::LeanObject,
    mut v_abbrev_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1737_ =
        l_Lean_ReducibilityHints_abbrev_elim(v_motive_1733_, v_t_1734_, v_h_1735_, v_abbrev_1736_);
    crate::leanh::lean_dec(v_t_1734_);
    return v_res_1737_;
}
pub unsafe fn l_Lean_ReducibilityHints_regular_elim___redArg(
    mut v_t_1738_: *mut crate::leanh::LeanObject,
    mut v_regular_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1738_, v_regular_1739_);
    return v___x_1740_;
}
pub unsafe fn l_Lean_ReducibilityHints_regular_elim___redArg___boxed(
    mut v_t_1741_: *mut crate::leanh::LeanObject,
    mut v_regular_1742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1743_ = l_Lean_ReducibilityHints_regular_elim___redArg(v_t_1741_, v_regular_1742_);
    crate::leanh::lean_dec(v_t_1741_);
    return v_res_1743_;
}
pub unsafe fn l_Lean_ReducibilityHints_regular_elim(
    mut v_motive_1744_: *mut crate::leanh::LeanObject,
    mut v_t_1745_: *mut crate::leanh::LeanObject,
    mut v_h_1746_: *mut crate::leanh::LeanObject,
    mut v_regular_1747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_1745_, v_regular_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_ReducibilityHints_regular_elim___boxed(
    mut v_motive_1749_: *mut crate::leanh::LeanObject,
    mut v_t_1750_: *mut crate::leanh::LeanObject,
    mut v_h_1751_: *mut crate::leanh::LeanObject,
    mut v_regular_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lean_ReducibilityHints_regular_elim(
        v_motive_1749_,
        v_t_1750_,
        v_h_1751_,
        v_regular_1752_,
    );
    crate::leanh::lean_dec(v_t_1750_);
    return v_res_1753_;
}
pub unsafe fn _init_l_Lean_instInhabitedReducibilityHints_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = crate::leanh::lean_box(0);
    return v___x_1754_;
}
pub unsafe fn _init_l_Lean_instInhabitedReducibilityHints() -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = crate::leanh::lean_box(0);
    return v___x_1755_;
}
pub unsafe fn l_Lean_instBEqReducibilityHints_beq(
    mut v_x_1756_: *mut crate::leanh::LeanObject,
    mut v_x_1757_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_1756_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_1757_) == 0 {
                let mut v___x_1758_: u8 = 0;
                v___x_1758_ = 1;
                return v___x_1758_;
            } else {
                let mut v___x_1759_: u8 = 0;
                v___x_1759_ = 0;
                return v___x_1759_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_1757_) == 1 {
                let mut v___x_1760_: u8 = 0;
                v___x_1760_ = 1;
                return v___x_1760_;
            } else {
                let mut v___x_1761_: u8 = 0;
                v___x_1761_ = 0;
                return v___x_1761_;
            }
        }
        _ => {
            if crate::leanh::lean_obj_tag(v_x_1757_) == 2 {
                let mut v_a_1762_: u32 = 0;
                let mut v_a_1763_: u32 = 0;
                let mut v___x_1764_: u8 = 0;
                v_a_1762_ = crate::leanh::lean_ctor_get_uint32(v_x_1756_, 0 as u32);
                v_a_1763_ = crate::leanh::lean_ctor_get_uint32(v_x_1757_, 0 as u32);
                v___x_1764_ = lean_uint32_dec_eq(v_a_1762_, v_a_1763_);
                return v___x_1764_;
            } else {
                let mut v___x_1765_: u8 = 0;
                v___x_1765_ = 0;
                return v___x_1765_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqReducibilityHints_beq___boxed(
    mut v_x_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1768_: u8 = 0;
    let mut v_r_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Lean_instBEqReducibilityHints_beq(v_x_1766_, v_x_1767_);
    crate::leanh::lean_dec(v_x_1767_);
    crate::leanh::lean_dec(v_x_1766_);
    v_r_1769_ = crate::leanh::lean_box((v_res_1768_) as usize);
    return v_r_1769_;
}
pub unsafe fn lean_mk_reducibility_hints_regular(
    mut v_h_1772_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = crate::leanh::lean_alloc_ctor(2, 0, (4) as u32);
    crate::leanh::lean_ctor_set_uint32(v___x_1773_, 0 as u32, v_h_1772_);
    return v___x_1773_;
}
pub unsafe fn l_Lean_mkReducibilityHintsRegularEx___boxed(
    mut v_h_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_1775_: u32 = 0;
    let mut v_res_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_1775_ = crate::leanh::lean_unbox_uint32(v_h_1774_);
    crate::leanh::lean_dec(v_h_1774_);
    v_res_1776_ = lean_mk_reducibility_hints_regular(v_h_boxed_1775_);
    return v_res_1776_;
}
pub unsafe fn lean_reducibility_hints_get_height(
    mut v_h_1777_: *mut crate::leanh::LeanObject,
) -> u32 {
    if crate::leanh::lean_obj_tag(v_h_1777_) == 2 {
        let mut v_a_1778_: u32 = 0;
        v_a_1778_ = crate::leanh::lean_ctor_get_uint32(v_h_1777_, 0 as u32);
        crate::leanh::lean_dec_ref_known(v_h_1777_, 0);
        return v_a_1778_;
    } else {
        let mut v___x_1779_: u32 = 0;
        crate::leanh::lean_dec(v_h_1777_);
        v___x_1779_ = 0;
        return v___x_1779_;
    }
}
pub unsafe fn l_Lean_ReducibilityHints_getHeightEx___boxed(
    mut v_h_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1781_: u32 = 0;
    let mut v_r_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1781_ = lean_reducibility_hints_get_height(v_h_1780_);
    v_r_1782_ = crate::leanh::lean_box_uint32(v_res_1781_);
    return v_r_1782_;
}
pub unsafe fn l_Lean_ReducibilityHints_lt(
    mut v_x_1783_: *mut crate::leanh::LeanObject,
    mut v_x_1784_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_1783_) {
        1 => {
            if crate::leanh::lean_obj_tag(v_x_1784_) == 1 {
                let mut v___x_1785_: u8 = 0;
                v___x_1785_ = 0;
                return v___x_1785_;
            } else {
                let mut v___x_1786_: u8 = 0;
                v___x_1786_ = 1;
                return v___x_1786_;
            }
        }
        2 => match crate::leanh::lean_obj_tag(v_x_1784_) {
            2 => {
                let mut v_a_1787_: u32 = 0;
                let mut v_a_1788_: u32 = 0;
                let mut v___x_1789_: u8 = 0;
                v_a_1787_ = crate::leanh::lean_ctor_get_uint32(v_x_1783_, 0 as u32);
                v_a_1788_ = crate::leanh::lean_ctor_get_uint32(v_x_1784_, 0 as u32);
                v___x_1789_ = lean_uint32_dec_lt(v_a_1788_, v_a_1787_);
                return v___x_1789_;
            }
            0 => {
                let mut v___x_1790_: u8 = 0;
                v___x_1790_ = 1;
                return v___x_1790_;
            }
            _ => {
                let mut v___x_1791_: u8 = 0;
                v___x_1791_ = 0;
                return v___x_1791_;
            }
        },
        _ => {
            let mut v___x_1792_: u8 = 0;
            v___x_1792_ = 0;
            return v___x_1792_;
        }
    }
}
pub unsafe fn l_Lean_ReducibilityHints_lt___boxed(
    mut v_x_1793_: *mut crate::leanh::LeanObject,
    mut v_x_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1795_: u8 = 0;
    let mut v_r_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = l_Lean_ReducibilityHints_lt(v_x_1793_, v_x_1794_);
    crate::leanh::lean_dec(v_x_1794_);
    crate::leanh::lean_dec(v_x_1793_);
    v_r_1796_ = crate::leanh::lean_box((v_res_1795_) as usize);
    return v_r_1796_;
}
pub unsafe fn l_Lean_ReducibilityHints_compare(
    mut v_x_1797_: *mut crate::leanh::LeanObject,
    mut v_x_1798_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_1797_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_1798_) == 0 {
                let mut v___x_1799_: u8 = 0;
                v___x_1799_ = 1;
                return v___x_1799_;
            } else {
                let mut v___x_1800_: u8 = 0;
                v___x_1800_ = 2;
                return v___x_1800_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_1798_) == 1 {
                let mut v___x_1801_: u8 = 0;
                v___x_1801_ = 1;
                return v___x_1801_;
            } else {
                let mut v___x_1802_: u8 = 0;
                v___x_1802_ = 0;
                return v___x_1802_;
            }
        }
        _ => match crate::leanh::lean_obj_tag(v_x_1798_) {
            0 => {
                let mut v___x_1803_: u8 = 0;
                v___x_1803_ = 0;
                return v___x_1803_;
            }
            1 => {
                let mut v___x_1804_: u8 = 0;
                v___x_1804_ = 2;
                return v___x_1804_;
            }
            _ => {
                let mut v_a_1805_: u32 = 0;
                let mut v_a_1806_: u32 = 0;
                let mut v___x_1807_: u8 = 0;
                v_a_1805_ = crate::leanh::lean_ctor_get_uint32(v_x_1797_, 0 as u32);
                v_a_1806_ = crate::leanh::lean_ctor_get_uint32(v_x_1798_, 0 as u32);
                v___x_1807_ = lean_uint32_dec_lt(v_a_1806_, v_a_1805_);
                if v___x_1807_ == 0 {
                    let mut v___x_1808_: u8 = 0;
                    v___x_1808_ = lean_uint32_dec_eq(v_a_1806_, v_a_1805_);
                    if v___x_1808_ == 0 {
                        let mut v___x_1809_: u8 = 0;
                        v___x_1809_ = 2;
                        return v___x_1809_;
                    } else {
                        let mut v___x_1810_: u8 = 0;
                        v___x_1810_ = 1;
                        return v___x_1810_;
                    }
                } else {
                    let mut v___x_1811_: u8 = 0;
                    v___x_1811_ = 0;
                    return v___x_1811_;
                }
            }
        },
    }
}
pub unsafe fn l_Lean_ReducibilityHints_compare___boxed(
    mut v_x_1812_: *mut crate::leanh::LeanObject,
    mut v_x_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1814_: u8 = 0;
    let mut v_r_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_ReducibilityHints_compare(v_x_1812_, v_x_1813_);
    crate::leanh::lean_dec(v_x_1813_);
    crate::leanh::lean_dec(v_x_1812_);
    v_r_1815_ = crate::leanh::lean_box((v_res_1814_) as usize);
    return v_r_1815_;
}
pub unsafe fn l_Lean_ReducibilityHints_isAbbrev(
    mut v_x_1818_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1818_) == 1 {
        let mut v___x_1819_: u8 = 0;
        v___x_1819_ = 1;
        return v___x_1819_;
    } else {
        let mut v___x_1820_: u8 = 0;
        v___x_1820_ = 0;
        return v___x_1820_;
    }
}
pub unsafe fn l_Lean_ReducibilityHints_isAbbrev___boxed(
    mut v_x_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1822_: u8 = 0;
    let mut v_r_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ = l_Lean_ReducibilityHints_isAbbrev(v_x_1821_);
    crate::leanh::lean_dec(v_x_1821_);
    v_r_1823_ = crate::leanh::lean_box((v_res_1822_) as usize);
    return v_r_1823_;
}
pub unsafe fn l_Lean_ReducibilityHints_isRegular(
    mut v_x_1824_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1824_) == 2 {
        let mut v___x_1825_: u8 = 0;
        v___x_1825_ = 1;
        return v___x_1825_;
    } else {
        let mut v___x_1826_: u8 = 0;
        v___x_1826_ = 0;
        return v___x_1826_;
    }
}
pub unsafe fn l_Lean_ReducibilityHints_isRegular___boxed(
    mut v_x_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1828_: u8 = 0;
    let mut v_r_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lean_ReducibilityHints_isRegular(v_x_1827_);
    crate::leanh::lean_dec(v_x_1827_);
    v_r_1829_ = crate::leanh::lean_box((v_res_1828_) as usize);
    return v_r_1829_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstantVal_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = crate::leanh::lean_box(0);
    v___x_1834_ = l_Lean_instInhabitedConstantVal_default___closed__1;
    v___x_1835_ = l_Lean_Expr_const___override(v___x_1834_, v___x_1833_);
    return v___x_1835_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstantVal_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstantVal_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstantVal_default___closed__2_once),
        _init_l_Lean_instInhabitedConstantVal_default___closed__2,
    );
    v___x_1837_ = crate::leanh::lean_box(0);
    v___x_1838_ = crate::leanh::lean_box(0);
    v___x_1839_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1839_, 0, v___x_1838_);
    crate::leanh::lean_ctor_set(v___x_1839_, 1, v___x_1837_);
    crate::leanh::lean_ctor_set(v___x_1839_, 2, v___x_1836_);
    return v___x_1839_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstantVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstantVal_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstantVal_default___closed__3_once),
        _init_l_Lean_instInhabitedConstantVal_default___closed__3,
    );
    return v___x_1840_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstantVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = l_Lean_instInhabitedConstantVal_default;
    return v___x_1841_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(
    mut v_x_1842_: *mut crate::leanh::LeanObject,
    mut v_x_1843_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: u8 = 0;
    let mut v_head_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1842_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_1843_) == 0 {
                        v___x_1844_ = 1;
                        return v___x_1844_;
                    } else {
                        v___x_1845_ = 0;
                        return v___x_1845_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1843_) == 0 {
                        v___x_1846_ = 0;
                        return v___x_1846_;
                    } else {
                        v_head_1847_ = crate::leanh::lean_ctor_get(v_x_1842_, 0);
                        v_tail_1848_ = crate::leanh::lean_ctor_get(v_x_1842_, 1);
                        v_head_1849_ = crate::leanh::lean_ctor_get(v_x_1843_, 0);
                        v_tail_1850_ = crate::leanh::lean_ctor_get(v_x_1843_, 1);
                        v___x_1851_ = lean_name_eq(v_head_1847_, v_head_1849_);
                        if v___x_1851_ == 0 {
                            return v___x_1851_;
                        } else {
                            v_x_1842_ = v_tail_1848_;
                            v_x_1843_ = v_tail_1850_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0___boxed(
    mut v_x_1853_: *mut crate::leanh::LeanObject,
    mut v_x_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1855_: u8 = 0;
    let mut v_r_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_x_1853_, v_x_1854_);
    crate::leanh::lean_dec(v_x_1854_);
    crate::leanh::lean_dec(v_x_1853_);
    v_r_1856_ = crate::leanh::lean_box((v_res_1855_) as usize);
    return v_r_1856_;
}
pub unsafe fn l_Lean_instBEqConstantVal_beq(
    mut v_x_1857_: *mut crate::leanh::LeanObject,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: u8 = 0;
    v_name_1859_ = crate::leanh::lean_ctor_get(v_x_1857_, 0);
    v_levelParams_1860_ = crate::leanh::lean_ctor_get(v_x_1857_, 1);
    v_type_1861_ = crate::leanh::lean_ctor_get(v_x_1857_, 2);
    v_name_1862_ = crate::leanh::lean_ctor_get(v_x_1858_, 0);
    v_levelParams_1863_ = crate::leanh::lean_ctor_get(v_x_1858_, 1);
    v_type_1864_ = crate::leanh::lean_ctor_get(v_x_1858_, 2);
    v___x_1865_ = lean_name_eq(v_name_1859_, v_name_1862_);
    if v___x_1865_ == 0 {
        return v___x_1865_;
    } else {
        let mut v___x_1866_: u8 = 0;
        v___x_1866_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(
            v_levelParams_1860_,
            v_levelParams_1863_,
        );
        if v___x_1866_ == 0 {
            return v___x_1866_;
        } else {
            let mut v___x_1867_: u8 = 0;
            v___x_1867_ = lean_expr_eqv(v_type_1861_, v_type_1864_);
            return v___x_1867_;
        }
    }
}
pub unsafe fn l_Lean_instBEqConstantVal_beq___boxed(
    mut v_x_1868_: *mut crate::leanh::LeanObject,
    mut v_x_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1870_: u8 = 0;
    let mut v_r_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Lean_instBEqConstantVal_beq(v_x_1868_, v_x_1869_);
    crate::leanh::lean_dec_ref(v_x_1869_);
    crate::leanh::lean_dec_ref(v_x_1868_);
    v_r_1871_ = crate::leanh::lean_box((v_res_1870_) as usize);
    return v_r_1871_;
}
pub unsafe fn _init_l_Lean_instInhabitedAxiomVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = 0;
    v___x_1875_ = l_Lean_instInhabitedConstantVal_default;
    v___x_1876_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1876_, 0, v___x_1875_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1876_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1874_,
    );
    return v___x_1876_;
}
pub unsafe fn _init_l_Lean_instInhabitedAxiomVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedAxiomVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedAxiomVal_default___closed__0_once),
        _init_l_Lean_instInhabitedAxiomVal_default___closed__0,
    );
    return v___x_1877_;
}
pub unsafe fn _init_l_Lean_instInhabitedAxiomVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1878_ = l_Lean_instInhabitedAxiomVal_default;
    return v___x_1878_;
}
pub unsafe fn l_Lean_instBEqAxiomVal_beq(
    mut v_x_1879_: *mut crate::leanh::LeanObject,
    mut v_x_1880_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toConstantVal_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_1882_: u8 = 0;
    let mut v_toConstantVal_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_1884_: u8 = 0;
    let mut v___x_1885_: u8 = 0;
    v_toConstantVal_1881_ = crate::leanh::lean_ctor_get(v_x_1879_, 0);
    v_isUnsafe_1882_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1879_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_toConstantVal_1883_ = crate::leanh::lean_ctor_get(v_x_1880_, 0);
    v_isUnsafe_1884_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1880_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_1885_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1881_, v_toConstantVal_1883_);
    if v___x_1885_ == 0 {
        return v___x_1885_;
    } else {
        if v_isUnsafe_1882_ == 0 {
            if v_isUnsafe_1884_ == 0 {
                return v___x_1885_;
            } else {
                return v_isUnsafe_1882_;
            }
        } else {
            return v_isUnsafe_1884_;
        }
    }
}
pub unsafe fn l_Lean_instBEqAxiomVal_beq___boxed(
    mut v_x_1886_: *mut crate::leanh::LeanObject,
    mut v_x_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1888_: u8 = 0;
    let mut v_r_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1888_ = l_Lean_instBEqAxiomVal_beq(v_x_1886_, v_x_1887_);
    crate::leanh::lean_dec_ref(v_x_1887_);
    crate::leanh::lean_dec_ref(v_x_1886_);
    v_r_1889_ = crate::leanh::lean_box((v_res_1888_) as usize);
    return v_r_1889_;
}
pub unsafe fn lean_mk_axiom_val(
    mut v_name_1892_: *mut crate::leanh::LeanObject,
    mut v_levelParams_1893_: *mut crate::leanh::LeanObject,
    mut v_type_1894_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_1895_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1896_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1896_, 0, v_name_1892_);
    crate::leanh::lean_ctor_set(v___x_1896_, 1, v_levelParams_1893_);
    crate::leanh::lean_ctor_set(v___x_1896_, 2, v_type_1894_);
    v___x_1897_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1897_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_isUnsafe_1895_,
    );
    return v___x_1897_;
}
pub unsafe fn l_Lean_mkAxiomValEx___boxed(
    mut v_name_1898_: *mut crate::leanh::LeanObject,
    mut v_levelParams_1899_: *mut crate::leanh::LeanObject,
    mut v_type_1900_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isUnsafe_boxed_1902_: u8 = 0;
    let mut v_res_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isUnsafe_boxed_1902_ = (crate::leanh::lean_unbox(v_isUnsafe_1901_) as u8);
    v_res_1903_ = lean_mk_axiom_val(
        v_name_1898_,
        v_levelParams_1899_,
        v_type_1900_,
        v_isUnsafe_boxed_1902_,
    );
    return v_res_1903_;
}
pub unsafe fn lean_axiom_val_is_unsafe(mut v_v_1904_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_isUnsafe_1905_: u8 = 0;
    v_isUnsafe_1905_ = crate::leanh::lean_ctor_get_uint8(
        v_v_1904_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_1904_);
    return v_isUnsafe_1905_;
}
pub unsafe fn l_Lean_AxiomVal_isUnsafeEx___boxed(
    mut v_v_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1907_: u8 = 0;
    let mut v_r_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1907_ = lean_axiom_val_is_unsafe(v_v_1906_);
    v_r_1908_ = crate::leanh::lean_box((v_res_1907_) as usize);
    return v_r_1908_;
}
pub unsafe fn l_Lean_DefinitionSafety_ctorIdx(mut v_x_1909_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_1909_ {
        0 => {
            let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1910_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1910_;
        }
        1 => {
            let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1911_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1911_;
        }
        _ => {
            let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1912_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1912_;
        }
    }
}
pub unsafe fn l_Lean_DefinitionSafety_ctorIdx___boxed(
    mut v_x_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1914_: u8 = 0;
    let mut v_res_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1914_ = (crate::leanh::lean_unbox(v_x_1913_) as u8);
    v_res_1915_ = l_Lean_DefinitionSafety_ctorIdx(v_x_boxed_1914_);
    return v_res_1915_;
}
pub unsafe fn l_Lean_DefinitionSafety_toCtorIdx(
    mut v_x_1916_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_DefinitionSafety_ctorIdx(v_x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_DefinitionSafety_toCtorIdx___boxed(
    mut v_x_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1919_: u8 = 0;
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1919_ = (crate::leanh::lean_unbox(v_x_1918_) as u8);
    v_res_1920_ = l_Lean_DefinitionSafety_toCtorIdx(v_x_4__boxed_1919_);
    return v_res_1920_;
}
pub unsafe fn l_Lean_DefinitionSafety_ctorElim___redArg(
    mut v_k_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1921_);
    return v_k_1921_;
}
pub unsafe fn l_Lean_DefinitionSafety_ctorElim___redArg___boxed(
    mut v_k_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_DefinitionSafety_ctorElim___redArg(v_k_1922_);
    crate::leanh::lean_dec(v_k_1922_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_DefinitionSafety_ctorElim(
    mut v_motive_1924_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1925_: *mut crate::leanh::LeanObject,
    mut v_t_1926_: u8,
    mut v_h_1927_: *mut crate::leanh::LeanObject,
    mut v_k_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1928_);
    return v_k_1928_;
}
pub unsafe fn l_Lean_DefinitionSafety_ctorElim___boxed(
    mut v_motive_1929_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1930_: *mut crate::leanh::LeanObject,
    mut v_t_1931_: *mut crate::leanh::LeanObject,
    mut v_h_1932_: *mut crate::leanh::LeanObject,
    mut v_k_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1934_: u8 = 0;
    let mut v_res_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1934_ = (crate::leanh::lean_unbox(v_t_1931_) as u8);
    v_res_1935_ = l_Lean_DefinitionSafety_ctorElim(
        v_motive_1929_,
        v_ctorIdx_1930_,
        v_t_boxed_1934_,
        v_h_1932_,
        v_k_1933_,
    );
    crate::leanh::lean_dec(v_k_1933_);
    crate::leanh::lean_dec(v_ctorIdx_1930_);
    return v_res_1935_;
}
pub unsafe fn l_Lean_DefinitionSafety_unsafe_elim___redArg(
    mut v_unsafe_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unsafe_1936_);
    return v_unsafe_1936_;
}
pub unsafe fn l_Lean_DefinitionSafety_unsafe_elim___redArg___boxed(
    mut v_unsafe_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = l_Lean_DefinitionSafety_unsafe_elim___redArg(v_unsafe_1937_);
    crate::leanh::lean_dec(v_unsafe_1937_);
    return v_res_1938_;
}
pub unsafe fn l_Lean_DefinitionSafety_unsafe_elim(
    mut v_motive_1939_: *mut crate::leanh::LeanObject,
    mut v_t_1940_: u8,
    mut v_h_1941_: *mut crate::leanh::LeanObject,
    mut v_unsafe_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_unsafe_1942_);
    return v_unsafe_1942_;
}
pub unsafe fn l_Lean_DefinitionSafety_unsafe_elim___boxed(
    mut v_motive_1943_: *mut crate::leanh::LeanObject,
    mut v_t_1944_: *mut crate::leanh::LeanObject,
    mut v_h_1945_: *mut crate::leanh::LeanObject,
    mut v_unsafe_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1947_: u8 = 0;
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1947_ = (crate::leanh::lean_unbox(v_t_1944_) as u8);
    v_res_1948_ = l_Lean_DefinitionSafety_unsafe_elim(
        v_motive_1943_,
        v_t_boxed_1947_,
        v_h_1945_,
        v_unsafe_1946_,
    );
    crate::leanh::lean_dec(v_unsafe_1946_);
    return v_res_1948_;
}
pub unsafe fn l_Lean_DefinitionSafety_safe_elim___redArg(
    mut v_safe_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_safe_1949_);
    return v_safe_1949_;
}
pub unsafe fn l_Lean_DefinitionSafety_safe_elim___redArg___boxed(
    mut v_safe_1950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ = l_Lean_DefinitionSafety_safe_elim___redArg(v_safe_1950_);
    crate::leanh::lean_dec(v_safe_1950_);
    return v_res_1951_;
}
pub unsafe fn l_Lean_DefinitionSafety_safe_elim(
    mut v_motive_1952_: *mut crate::leanh::LeanObject,
    mut v_t_1953_: u8,
    mut v_h_1954_: *mut crate::leanh::LeanObject,
    mut v_safe_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_safe_1955_);
    return v_safe_1955_;
}
pub unsafe fn l_Lean_DefinitionSafety_safe_elim___boxed(
    mut v_motive_1956_: *mut crate::leanh::LeanObject,
    mut v_t_1957_: *mut crate::leanh::LeanObject,
    mut v_h_1958_: *mut crate::leanh::LeanObject,
    mut v_safe_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1960_: u8 = 0;
    let mut v_res_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1960_ = (crate::leanh::lean_unbox(v_t_1957_) as u8);
    v_res_1961_ =
        l_Lean_DefinitionSafety_safe_elim(v_motive_1956_, v_t_boxed_1960_, v_h_1958_, v_safe_1959_);
    crate::leanh::lean_dec(v_safe_1959_);
    return v_res_1961_;
}
pub unsafe fn l_Lean_DefinitionSafety_partial_elim___redArg(
    mut v_partial_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_partial_1962_);
    return v_partial_1962_;
}
pub unsafe fn l_Lean_DefinitionSafety_partial_elim___redArg___boxed(
    mut v_partial_1963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l_Lean_DefinitionSafety_partial_elim___redArg(v_partial_1963_);
    crate::leanh::lean_dec(v_partial_1963_);
    return v_res_1964_;
}
pub unsafe fn l_Lean_DefinitionSafety_partial_elim(
    mut v_motive_1965_: *mut crate::leanh::LeanObject,
    mut v_t_1966_: u8,
    mut v_h_1967_: *mut crate::leanh::LeanObject,
    mut v_partial_1968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_partial_1968_);
    return v_partial_1968_;
}
pub unsafe fn l_Lean_DefinitionSafety_partial_elim___boxed(
    mut v_motive_1969_: *mut crate::leanh::LeanObject,
    mut v_t_1970_: *mut crate::leanh::LeanObject,
    mut v_h_1971_: *mut crate::leanh::LeanObject,
    mut v_partial_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1973_: u8 = 0;
    let mut v_res_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1973_ = (crate::leanh::lean_unbox(v_t_1970_) as u8);
    v_res_1974_ = l_Lean_DefinitionSafety_partial_elim(
        v_motive_1969_,
        v_t_boxed_1973_,
        v_h_1971_,
        v_partial_1972_,
    );
    crate::leanh::lean_dec(v_partial_1972_);
    return v_res_1974_;
}
pub unsafe fn _init_l_Lean_instInhabitedDefinitionSafety_default() -> u8 {
    let mut v___x_1975_: u8 = 0;
    v___x_1975_ = 0;
    return v___x_1975_;
}
pub unsafe fn _init_l_Lean_instInhabitedDefinitionSafety() -> u8 {
    let mut v___x_1976_: u8 = 0;
    v___x_1976_ = 0;
    return v___x_1976_;
}
pub unsafe fn l_Lean_instBEqDefinitionSafety_beq(mut v_x_1977_: u8, mut v_y_1978_: u8) -> u8 {
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: u8 = 0;
    v___x_1979_ = l_Lean_DefinitionSafety_ctorIdx(v_x_1977_);
    v___x_1980_ = l_Lean_DefinitionSafety_ctorIdx(v_y_1978_);
    v___x_1981_ = lean_nat_dec_eq(v___x_1979_, v___x_1980_);
    crate::leanh::lean_dec(v___x_1980_);
    crate::leanh::lean_dec(v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn l_Lean_instBEqDefinitionSafety_beq___boxed(
    mut v_x_1982_: *mut crate::leanh::LeanObject,
    mut v_y_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_1984_: u8 = 0;
    let mut v_y_18__boxed_1985_: u8 = 0;
    let mut v_res_1986_: u8 = 0;
    let mut v_r_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1984_ = (crate::leanh::lean_unbox(v_x_1982_) as u8);
    v_y_18__boxed_1985_ = (crate::leanh::lean_unbox(v_y_1983_) as u8);
    v_res_1986_ = l_Lean_instBEqDefinitionSafety_beq(v_x_17__boxed_1984_, v_y_18__boxed_1985_);
    v_r_1987_ = crate::leanh::lean_box((v_res_1986_) as usize);
    return v_r_1987_;
}
pub unsafe fn _init_l_Lean_instReprDefinitionSafety_repr___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1999_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2000_ = lean_nat_to_int(v___x_1999_);
    return v___x_2000_;
}
pub unsafe fn _init_l_Lean_instReprDefinitionSafety_repr___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2002_ = lean_nat_to_int(v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn l_Lean_instReprDefinitionSafety_repr(
    mut v_x_2003_: u8,
    mut v_prec_2004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: u8 = 0;
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2003_ {
                0 => {
                    v___x_2026_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2027_ = lean_nat_dec_le(v___x_2026_, v_prec_2004_);
                    if v___x_2027_ == 0 {
                        v___x_2028_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__6_once
                            ),
                            _init_l_Lean_instReprDefinitionSafety_repr___closed__6,
                        );
                        v___y_2006_ = v___x_2028_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2029_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__7_once
                            ),
                            _init_l_Lean_instReprDefinitionSafety_repr___closed__7,
                        );
                        v___y_2006_ = v___x_2029_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2030_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2031_ = lean_nat_dec_le(v___x_2030_, v_prec_2004_);
                    if v___x_2031_ == 0 {
                        v___x_2032_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__6_once
                            ),
                            _init_l_Lean_instReprDefinitionSafety_repr___closed__6,
                        );
                        v___y_2013_ = v___x_2032_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2033_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__7_once
                            ),
                            _init_l_Lean_instReprDefinitionSafety_repr___closed__7,
                        );
                        v___y_2013_ = v___x_2033_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_2034_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2035_ = lean_nat_dec_le(v___x_2034_, v_prec_2004_);
                    if v___x_2035_ == 0 {
                        v___x_2036_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__6_once
                            ),
                            _init_l_Lean_instReprDefinitionSafety_repr___closed__6,
                        );
                        v___y_2020_ = v___x_2036_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2037_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprDefinitionSafety_repr___closed__7_once
                            ),
                            _init_l_Lean_instReprDefinitionSafety_repr___closed__7,
                        );
                        v___y_2020_ = v___x_2037_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2007_ = l_Lean_instReprDefinitionSafety_repr___closed__1;
                crate::leanh::lean_inc(v___y_2006_);
                v___x_2008_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2008_, 0, v___y_2006_);
                crate::leanh::lean_ctor_set(v___x_2008_, 1, v___x_2007_);
                v___x_2009_ = 0;
                v___x_2010_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2010_, 0, v___x_2008_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2010_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2009_,
                );
                v___x_2011_ = l_Repr_addAppParen(v___x_2010_, v_prec_2004_);
                return v___x_2011_;
            }
            2 => {
                v___x_2014_ = l_Lean_instReprDefinitionSafety_repr___closed__3;
                crate::leanh::lean_inc(v___y_2013_);
                v___x_2015_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2015_, 0, v___y_2013_);
                crate::leanh::lean_ctor_set(v___x_2015_, 1, v___x_2014_);
                v___x_2016_ = 0;
                v___x_2017_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2015_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2017_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2016_,
                );
                v___x_2018_ = l_Repr_addAppParen(v___x_2017_, v_prec_2004_);
                return v___x_2018_;
            }
            3 => {
                v___x_2021_ = l_Lean_instReprDefinitionSafety_repr___closed__5;
                crate::leanh::lean_inc(v___y_2020_);
                v___x_2022_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2022_, 0, v___y_2020_);
                crate::leanh::lean_ctor_set(v___x_2022_, 1, v___x_2021_);
                v___x_2023_ = 0;
                v___x_2024_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2024_, 0, v___x_2022_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2024_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2023_,
                );
                v___x_2025_ = l_Repr_addAppParen(v___x_2024_, v_prec_2004_);
                return v___x_2025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprDefinitionSafety_repr___boxed(
    mut v_x_2038_: *mut crate::leanh::LeanObject,
    mut v_prec_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_177__boxed_2040_: u8 = 0;
    let mut v_res_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_2040_ = (crate::leanh::lean_unbox(v_x_2038_) as u8);
    v_res_2041_ = l_Lean_instReprDefinitionSafety_repr(v_x_177__boxed_2040_, v_prec_2039_);
    crate::leanh::lean_dec(v_prec_2039_);
    return v_res_2041_;
}
pub unsafe fn _init_l_Lean_instInhabitedDefinitionVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = crate::leanh::lean_box(0);
    v___x_2045_ = l_Lean_instInhabitedConstantVal_default___closed__1;
    v___x_2046_ = l_Lean_Expr_const___override(v___x_2045_, v___x_2044_);
    return v___x_2046_;
}
pub unsafe fn _init_l_Lean_instInhabitedDefinitionVal_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_Lean_instInhabitedDefinitionVal_default___closed__1;
    v___x_2051_ = 0;
    v___x_2052_ = crate::leanh::lean_box(0);
    v___x_2053_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__0_once),
        _init_l_Lean_instInhabitedDefinitionVal_default___closed__0,
    );
    v___x_2054_ = l_Lean_instInhabitedConstantVal_default;
    v___x_2055_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2054_);
    crate::leanh::lean_ctor_set(v___x_2055_, 1, v___x_2053_);
    crate::leanh::lean_ctor_set(v___x_2055_, 2, v___x_2052_);
    crate::leanh::lean_ctor_set(v___x_2055_, 3, v___x_2050_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2055_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_2051_,
    );
    return v___x_2055_;
}
pub unsafe fn _init_l_Lean_instInhabitedDefinitionVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__2_once),
        _init_l_Lean_instInhabitedDefinitionVal_default___closed__2,
    );
    return v___x_2056_;
}
pub unsafe fn _init_l_Lean_instInhabitedDefinitionVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = l_Lean_instInhabitedDefinitionVal_default;
    return v___x_2057_;
}
pub unsafe fn l_Lean_instBEqDefinitionVal_beq(
    mut v_x_2058_: *mut crate::leanh::LeanObject,
    mut v_x_2059_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toConstantVal_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hints_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safety_2063_: u8 = 0;
    let mut v_all_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hints_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safety_2068_: u8 = 0;
    let mut v_all_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: u8 = 0;
    v_toConstantVal_2060_ = crate::leanh::lean_ctor_get(v_x_2058_, 0);
    v_value_2061_ = crate::leanh::lean_ctor_get(v_x_2058_, 1);
    v_hints_2062_ = crate::leanh::lean_ctor_get(v_x_2058_, 2);
    v_safety_2063_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2058_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
    );
    v_all_2064_ = crate::leanh::lean_ctor_get(v_x_2058_, 3);
    v_toConstantVal_2065_ = crate::leanh::lean_ctor_get(v_x_2059_, 0);
    v_value_2066_ = crate::leanh::lean_ctor_get(v_x_2059_, 1);
    v_hints_2067_ = crate::leanh::lean_ctor_get(v_x_2059_, 2);
    v_safety_2068_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2059_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
    );
    v_all_2069_ = crate::leanh::lean_ctor_get(v_x_2059_, 3);
    v___x_2070_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_2060_, v_toConstantVal_2065_);
    if v___x_2070_ == 0 {
        return v___x_2070_;
    } else {
        let mut v___x_2071_: u8 = 0;
        v___x_2071_ = lean_expr_eqv(v_value_2061_, v_value_2066_);
        if v___x_2071_ == 0 {
            return v___x_2071_;
        } else {
            let mut v___x_2072_: u8 = 0;
            v___x_2072_ = l_Lean_instBEqReducibilityHints_beq(v_hints_2062_, v_hints_2067_);
            if v___x_2072_ == 0 {
                return v___x_2072_;
            } else {
                let mut v___x_2073_: u8 = 0;
                v___x_2073_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_2063_, v_safety_2068_);
                if v___x_2073_ == 0 {
                    return v___x_2073_;
                } else {
                    let mut v___x_2074_: u8 = 0;
                    v___x_2074_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(
                        v_all_2064_,
                        v_all_2069_,
                    );
                    return v___x_2074_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqDefinitionVal_beq___boxed(
    mut v_x_2075_: *mut crate::leanh::LeanObject,
    mut v_x_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2077_: u8 = 0;
    let mut v_r_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2077_ = l_Lean_instBEqDefinitionVal_beq(v_x_2075_, v_x_2076_);
    crate::leanh::lean_dec_ref(v_x_2076_);
    crate::leanh::lean_dec_ref(v_x_2075_);
    v_r_2078_ = crate::leanh::lean_box((v_res_2077_) as usize);
    return v_r_2078_;
}
pub unsafe fn lean_mk_definition_val(
    mut v_name_2081_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2082_: *mut crate::leanh::LeanObject,
    mut v_type_2083_: *mut crate::leanh::LeanObject,
    mut v_value_2084_: *mut crate::leanh::LeanObject,
    mut v_hints_2085_: *mut crate::leanh::LeanObject,
    mut v_safety_2086_: u8,
    mut v_all_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2088_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2088_, 0, v_name_2081_);
    crate::leanh::lean_ctor_set(v___x_2088_, 1, v_levelParams_2082_);
    crate::leanh::lean_ctor_set(v___x_2088_, 2, v_type_2083_);
    v___x_2089_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2089_, 0, v___x_2088_);
    crate::leanh::lean_ctor_set(v___x_2089_, 1, v_value_2084_);
    crate::leanh::lean_ctor_set(v___x_2089_, 2, v_hints_2085_);
    crate::leanh::lean_ctor_set(v___x_2089_, 3, v_all_2087_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2089_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v_safety_2086_,
    );
    return v___x_2089_;
}
pub unsafe fn l_Lean_mkDefinitionValEx___boxed(
    mut v_name_2090_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2091_: *mut crate::leanh::LeanObject,
    mut v_type_2092_: *mut crate::leanh::LeanObject,
    mut v_value_2093_: *mut crate::leanh::LeanObject,
    mut v_hints_2094_: *mut crate::leanh::LeanObject,
    mut v_safety_2095_: *mut crate::leanh::LeanObject,
    mut v_all_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_safety_boxed_2097_: u8 = 0;
    let mut v_res_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_safety_boxed_2097_ = (crate::leanh::lean_unbox(v_safety_2095_) as u8);
    v_res_2098_ = lean_mk_definition_val(
        v_name_2090_,
        v_levelParams_2091_,
        v_type_2092_,
        v_value_2093_,
        v_hints_2094_,
        v_safety_boxed_2097_,
        v_all_2096_,
    );
    return v_res_2098_;
}
pub unsafe fn lean_definition_val_get_safety(mut v_v_2099_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_safety_2100_: u8 = 0;
    v_safety_2100_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2099_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2099_);
    return v_safety_2100_;
}
pub unsafe fn l_Lean_DefinitionVal_getSafetyEx___boxed(
    mut v_v_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2102_: u8 = 0;
    let mut v_r_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2102_ = lean_definition_val_get_safety(v_v_2101_);
    v_r_2103_ = crate::leanh::lean_box((v_res_2102_) as usize);
    return v_r_2103_;
}
pub unsafe fn _init_l_Lean_instInhabitedTheoremVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = l_Lean_instInhabitedDefinitionVal_default___closed__1;
    v___x_2105_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__0_once),
        _init_l_Lean_instInhabitedDefinitionVal_default___closed__0,
    );
    v___x_2106_ = l_Lean_instInhabitedConstantVal_default;
    v___x_2107_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2106_);
    crate::leanh::lean_ctor_set(v___x_2107_, 1, v___x_2105_);
    crate::leanh::lean_ctor_set(v___x_2107_, 2, v___x_2104_);
    return v___x_2107_;
}
pub unsafe fn _init_l_Lean_instInhabitedTheoremVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTheoremVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedTheoremVal_default___closed__0_once),
        _init_l_Lean_instInhabitedTheoremVal_default___closed__0,
    );
    return v___x_2108_;
}
pub unsafe fn _init_l_Lean_instInhabitedTheoremVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2109_ = l_Lean_instInhabitedTheoremVal_default;
    return v___x_2109_;
}
pub unsafe fn l_Lean_instBEqTheoremVal_beq(
    mut v_x_2110_: *mut crate::leanh::LeanObject,
    mut v_x_2111_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toConstantVal_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: u8 = 0;
    v_toConstantVal_2112_ = crate::leanh::lean_ctor_get(v_x_2110_, 0);
    v_value_2113_ = crate::leanh::lean_ctor_get(v_x_2110_, 1);
    v_all_2114_ = crate::leanh::lean_ctor_get(v_x_2110_, 2);
    v_toConstantVal_2115_ = crate::leanh::lean_ctor_get(v_x_2111_, 0);
    v_value_2116_ = crate::leanh::lean_ctor_get(v_x_2111_, 1);
    v_all_2117_ = crate::leanh::lean_ctor_get(v_x_2111_, 2);
    v___x_2118_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_2112_, v_toConstantVal_2115_);
    if v___x_2118_ == 0 {
        return v___x_2118_;
    } else {
        let mut v___x_2119_: u8 = 0;
        v___x_2119_ = lean_expr_eqv(v_value_2113_, v_value_2116_);
        if v___x_2119_ == 0 {
            return v___x_2119_;
        } else {
            let mut v___x_2120_: u8 = 0;
            v___x_2120_ =
                l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_2114_, v_all_2117_);
            return v___x_2120_;
        }
    }
}
pub unsafe fn l_Lean_instBEqTheoremVal_beq___boxed(
    mut v_x_2121_: *mut crate::leanh::LeanObject,
    mut v_x_2122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2123_: u8 = 0;
    let mut v_r_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2123_ = l_Lean_instBEqTheoremVal_beq(v_x_2121_, v_x_2122_);
    crate::leanh::lean_dec_ref(v_x_2122_);
    crate::leanh::lean_dec_ref(v_x_2121_);
    v_r_2124_ = crate::leanh::lean_box((v_res_2123_) as usize);
    return v_r_2124_;
}
pub unsafe fn lean_mk_theorem_val(
    mut v_name_2127_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2128_: *mut crate::leanh::LeanObject,
    mut v_type_2129_: *mut crate::leanh::LeanObject,
    mut v_value_2130_: *mut crate::leanh::LeanObject,
    mut v_all_2131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2132_, 0, v_name_2127_);
    crate::leanh::lean_ctor_set(v___x_2132_, 1, v_levelParams_2128_);
    crate::leanh::lean_ctor_set(v___x_2132_, 2, v_type_2129_);
    v___x_2133_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2132_);
    crate::leanh::lean_ctor_set(v___x_2133_, 1, v_value_2130_);
    crate::leanh::lean_ctor_set(v___x_2133_, 2, v_all_2131_);
    return v___x_2133_;
}
pub unsafe fn _init_l_Lean_instInhabitedOpaqueVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = l_Lean_instInhabitedDefinitionVal_default___closed__1;
    v___x_2135_ = 0;
    v___x_2136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDefinitionVal_default___closed__0_once),
        _init_l_Lean_instInhabitedDefinitionVal_default___closed__0,
    );
    v___x_2137_ = l_Lean_instInhabitedConstantVal_default;
    v___x_2138_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2137_);
    crate::leanh::lean_ctor_set(v___x_2138_, 1, v___x_2136_);
    crate::leanh::lean_ctor_set(v___x_2138_, 2, v___x_2134_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2138_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2135_,
    );
    return v___x_2138_;
}
pub unsafe fn _init_l_Lean_instInhabitedOpaqueVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedOpaqueVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedOpaqueVal_default___closed__0_once),
        _init_l_Lean_instInhabitedOpaqueVal_default___closed__0,
    );
    return v___x_2139_;
}
pub unsafe fn _init_l_Lean_instInhabitedOpaqueVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = l_Lean_instInhabitedOpaqueVal_default;
    return v___x_2140_;
}
pub unsafe fn l_Lean_instBEqOpaqueVal_beq(
    mut v_x_2141_: *mut crate::leanh::LeanObject,
    mut v_x_2142_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toConstantVal_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_2145_: u8 = 0;
    let mut v_all_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_2149_: u8 = 0;
    let mut v_all_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: u8 = 0;
    let mut v___x_2153_: u8 = 0;
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toConstantVal_2143_ = crate::leanh::lean_ctor_get(v_x_2141_, 0);
                v_value_2144_ = crate::leanh::lean_ctor_get(v_x_2141_, 1);
                v_isUnsafe_2145_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2141_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_all_2146_ = crate::leanh::lean_ctor_get(v_x_2141_, 2);
                v_toConstantVal_2147_ = crate::leanh::lean_ctor_get(v_x_2142_, 0);
                v_value_2148_ = crate::leanh::lean_ctor_get(v_x_2142_, 1);
                v_isUnsafe_2149_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2142_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_all_2150_ = crate::leanh::lean_ctor_get(v_x_2142_, 2);
                v___x_2154_ =
                    l_Lean_instBEqConstantVal_beq(v_toConstantVal_2143_, v_toConstantVal_2147_);
                if v___x_2154_ == 0 {
                    return v___x_2154_;
                } else {
                    v___x_2155_ = lean_expr_eqv(v_value_2144_, v_value_2148_);
                    if v___x_2155_ == 0 {
                        return v___x_2155_;
                    } else {
                        if v_isUnsafe_2145_ == 0 {
                            if v_isUnsafe_2149_ == 0 {
                                v___y_2152_ = v___x_2155_;
                                state = 1;
                                continue;
                            } else {
                                return v_isUnsafe_2145_;
                            }
                        } else {
                            v___y_2152_ = v_isUnsafe_2149_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_2152_ == 0 {
                    return v___y_2152_;
                } else {
                    v___x_2153_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(
                        v_all_2146_,
                        v_all_2150_,
                    );
                    return v___x_2153_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instBEqOpaqueVal_beq___boxed(
    mut v_x_2156_: *mut crate::leanh::LeanObject,
    mut v_x_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2158_: u8 = 0;
    let mut v_r_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2158_ = l_Lean_instBEqOpaqueVal_beq(v_x_2156_, v_x_2157_);
    crate::leanh::lean_dec_ref(v_x_2157_);
    crate::leanh::lean_dec_ref(v_x_2156_);
    v_r_2159_ = crate::leanh::lean_box((v_res_2158_) as usize);
    return v_r_2159_;
}
pub unsafe fn lean_mk_opaque_val(
    mut v_name_2162_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2163_: *mut crate::leanh::LeanObject,
    mut v_type_2164_: *mut crate::leanh::LeanObject,
    mut v_value_2165_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2166_: u8,
    mut v_all_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2168_, 0, v_name_2162_);
    crate::leanh::lean_ctor_set(v___x_2168_, 1, v_levelParams_2163_);
    crate::leanh::lean_ctor_set(v___x_2168_, 2, v_type_2164_);
    v___x_2169_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2168_);
    crate::leanh::lean_ctor_set(v___x_2169_, 1, v_value_2165_);
    crate::leanh::lean_ctor_set(v___x_2169_, 2, v_all_2167_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2169_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_isUnsafe_2166_,
    );
    return v___x_2169_;
}
pub unsafe fn l_Lean_mkOpaqueValEx___boxed(
    mut v_name_2170_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2171_: *mut crate::leanh::LeanObject,
    mut v_type_2172_: *mut crate::leanh::LeanObject,
    mut v_value_2173_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2174_: *mut crate::leanh::LeanObject,
    mut v_all_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isUnsafe_boxed_2176_: u8 = 0;
    let mut v_res_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isUnsafe_boxed_2176_ = (crate::leanh::lean_unbox(v_isUnsafe_2174_) as u8);
    v_res_2177_ = lean_mk_opaque_val(
        v_name_2170_,
        v_levelParams_2171_,
        v_type_2172_,
        v_value_2173_,
        v_isUnsafe_boxed_2176_,
        v_all_2175_,
    );
    return v_res_2177_;
}
pub unsafe fn lean_opaque_val_is_unsafe(mut v_v_2178_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_isUnsafe_2179_: u8 = 0;
    v_isUnsafe_2179_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2178_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2178_);
    return v_isUnsafe_2179_;
}
pub unsafe fn l_Lean_OpaqueVal_isUnsafeEx___boxed(
    mut v_v_2180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2181_: u8 = 0;
    let mut v_r_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2181_ = lean_opaque_val_is_unsafe(v_v_2180_);
    v_r_2182_ = crate::leanh::lean_box((v_res_2181_) as usize);
    return v_r_2182_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstructor_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = crate::leanh::lean_box(0);
    v___x_2184_ = l_Lean_instInhabitedConstantVal_default___closed__1;
    v___x_2185_ = l_Lean_Expr_const___override(v___x_2184_, v___x_2183_);
    return v___x_2185_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstructor_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__0_once),
        _init_l_Lean_instInhabitedConstructor_default___closed__0,
    );
    v___x_2187_ = crate::leanh::lean_box(0);
    v___x_2188_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2187_);
    crate::leanh::lean_ctor_set(v___x_2188_, 1, v___x_2186_);
    return v___x_2188_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstructor_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2189_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__1_once),
        _init_l_Lean_instInhabitedConstructor_default___closed__1,
    );
    return v___x_2189_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstructor() -> *mut crate::leanh::LeanObject {
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = l_Lean_instInhabitedConstructor_default;
    return v___x_2190_;
}
pub unsafe fn l_Lean_instBEqConstructor_beq(
    mut v_x_2191_: *mut crate::leanh::LeanObject,
    mut v_x_2192_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: u8 = 0;
    v_name_2193_ = crate::leanh::lean_ctor_get(v_x_2191_, 0);
    v_type_2194_ = crate::leanh::lean_ctor_get(v_x_2191_, 1);
    v_name_2195_ = crate::leanh::lean_ctor_get(v_x_2192_, 0);
    v_type_2196_ = crate::leanh::lean_ctor_get(v_x_2192_, 1);
    v___x_2197_ = lean_name_eq(v_name_2193_, v_name_2195_);
    if v___x_2197_ == 0 {
        return v___x_2197_;
    } else {
        let mut v___x_2198_: u8 = 0;
        v___x_2198_ = lean_expr_eqv(v_type_2194_, v_type_2196_);
        return v___x_2198_;
    }
}
pub unsafe fn l_Lean_instBEqConstructor_beq___boxed(
    mut v_x_2199_: *mut crate::leanh::LeanObject,
    mut v_x_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2201_: u8 = 0;
    let mut v_r_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2201_ = l_Lean_instBEqConstructor_beq(v_x_2199_, v_x_2200_);
    crate::leanh::lean_dec_ref(v_x_2200_);
    crate::leanh::lean_dec_ref(v_x_2199_);
    v_r_2202_ = crate::leanh::lean_box((v_res_2201_) as usize);
    return v_r_2202_;
}
pub unsafe fn _init_l_Lean_instInhabitedInductiveType_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2205_ = crate::leanh::lean_box(0);
    v___x_2206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__0_once),
        _init_l_Lean_instInhabitedConstructor_default___closed__0,
    );
    v___x_2207_ = crate::leanh::lean_box(0);
    v___x_2208_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2208_, 0, v___x_2207_);
    crate::leanh::lean_ctor_set(v___x_2208_, 1, v___x_2206_);
    crate::leanh::lean_ctor_set(v___x_2208_, 2, v___x_2205_);
    return v___x_2208_;
}
pub unsafe fn _init_l_Lean_instInhabitedInductiveType_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedInductiveType_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedInductiveType_default___closed__0_once),
        _init_l_Lean_instInhabitedInductiveType_default___closed__0,
    );
    return v___x_2209_;
}
pub unsafe fn _init_l_Lean_instInhabitedInductiveType() -> *mut crate::leanh::LeanObject {
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_Lean_instInhabitedInductiveType_default;
    return v___x_2210_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(
    mut v_x_2211_: *mut crate::leanh::LeanObject,
    mut v_x_2212_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: u8 = 0;
    let mut v___x_2215_: u8 = 0;
    let mut v_head_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2211_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_2212_) == 0 {
                        v___x_2213_ = 1;
                        return v___x_2213_;
                    } else {
                        v___x_2214_ = 0;
                        return v___x_2214_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_2212_) == 0 {
                        v___x_2215_ = 0;
                        return v___x_2215_;
                    } else {
                        v_head_2216_ = crate::leanh::lean_ctor_get(v_x_2211_, 0);
                        v_tail_2217_ = crate::leanh::lean_ctor_get(v_x_2211_, 1);
                        v_head_2218_ = crate::leanh::lean_ctor_get(v_x_2212_, 0);
                        v_tail_2219_ = crate::leanh::lean_ctor_get(v_x_2212_, 1);
                        v___x_2220_ = l_Lean_instBEqConstructor_beq(v_head_2216_, v_head_2218_);
                        if v___x_2220_ == 0 {
                            return v___x_2220_;
                        } else {
                            v_x_2211_ = v_tail_2217_;
                            v_x_2212_ = v_tail_2219_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(
    mut v_x_2222_: *mut crate::leanh::LeanObject,
    mut v_x_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2224_: u8 = 0;
    let mut v_r_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_2222_, v_x_2223_);
    crate::leanh::lean_dec(v_x_2223_);
    crate::leanh::lean_dec(v_x_2222_);
    v_r_2225_ = crate::leanh::lean_box((v_res_2224_) as usize);
    return v_r_2225_;
}
pub unsafe fn l_Lean_instBEqInductiveType_beq(
    mut v_x_2226_: *mut crate::leanh::LeanObject,
    mut v_x_2227_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    v_name_2228_ = crate::leanh::lean_ctor_get(v_x_2226_, 0);
    v_type_2229_ = crate::leanh::lean_ctor_get(v_x_2226_, 1);
    v_ctors_2230_ = crate::leanh::lean_ctor_get(v_x_2226_, 2);
    v_name_2231_ = crate::leanh::lean_ctor_get(v_x_2227_, 0);
    v_type_2232_ = crate::leanh::lean_ctor_get(v_x_2227_, 1);
    v_ctors_2233_ = crate::leanh::lean_ctor_get(v_x_2227_, 2);
    v___x_2234_ = lean_name_eq(v_name_2228_, v_name_2231_);
    if v___x_2234_ == 0 {
        return v___x_2234_;
    } else {
        let mut v___x_2235_: u8 = 0;
        v___x_2235_ = lean_expr_eqv(v_type_2229_, v_type_2232_);
        if v___x_2235_ == 0 {
            return v___x_2235_;
        } else {
            let mut v___x_2236_: u8 = 0;
            v___x_2236_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(
                v_ctors_2230_,
                v_ctors_2233_,
            );
            return v___x_2236_;
        }
    }
}
pub unsafe fn l_Lean_instBEqInductiveType_beq___boxed(
    mut v_x_2237_: *mut crate::leanh::LeanObject,
    mut v_x_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2239_: u8 = 0;
    let mut v_r_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Lean_instBEqInductiveType_beq(v_x_2237_, v_x_2238_);
    crate::leanh::lean_dec_ref(v_x_2238_);
    crate::leanh::lean_dec_ref(v_x_2237_);
    v_r_2240_ = crate::leanh::lean_box((v_res_2239_) as usize);
    return v_r_2240_;
}
pub unsafe fn l_Lean_Declaration_ctorIdx(
    mut v_x_2243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2243_) {
        0 => {
            let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2244_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2244_;
        }
        1 => {
            let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2245_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2245_;
        }
        2 => {
            let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2246_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2246_;
        }
        3 => {
            let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2247_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2247_;
        }
        4 => {
            let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2248_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2248_;
        }
        5 => {
            let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2249_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_2249_;
        }
        _ => {
            let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2250_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_2250_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_ctorIdx___boxed(
    mut v_x_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_Declaration_ctorIdx(v_x_2251_);
    crate::leanh::lean_dec(v_x_2251_);
    return v_res_2252_;
}
pub unsafe fn l_Lean_Declaration_ctorElim___redArg(
    mut v_t_2253_: *mut crate::leanh::LeanObject,
    mut v_k_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_2253_) {
        4 => {
            return v_k_2254_;
        }
        5 => {
            let mut v_defns_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_defns_2255_ = crate::leanh::lean_ctor_get(v_t_2253_, 0);
            crate::leanh::lean_inc(v_defns_2255_);
            crate::leanh::lean_dec_ref_known(v_t_2253_, 1);
            v___x_2256_ = crate::leanh::lean_apply_1(v_k_2254_, v_defns_2255_);
            return v___x_2256_;
        }
        6 => {
            let mut v_lparams_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_nparams_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_types_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isUnsafe_2260_: u8 = 0;
            let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_lparams_2257_ = crate::leanh::lean_ctor_get(v_t_2253_, 0);
            crate::leanh::lean_inc(v_lparams_2257_);
            v_nparams_2258_ = crate::leanh::lean_ctor_get(v_t_2253_, 1);
            crate::leanh::lean_inc(v_nparams_2258_);
            v_types_2259_ = crate::leanh::lean_ctor_get(v_t_2253_, 2);
            crate::leanh::lean_inc(v_types_2259_);
            v_isUnsafe_2260_ = crate::leanh::lean_ctor_get_uint8(
                v_t_2253_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            crate::leanh::lean_dec_ref_known(v_t_2253_, 3);
            v___x_2261_ = crate::leanh::lean_box((v_isUnsafe_2260_) as usize);
            v___x_2262_ = crate::leanh::lean_apply_4(
                v_k_2254_,
                v_lparams_2257_,
                v_nparams_2258_,
                v_types_2259_,
                v___x_2261_,
            );
            return v___x_2262_;
        }
        _ => {
            let mut v_val_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2263_ = crate::leanh::lean_ctor_get(v_t_2253_, 0);
            crate::leanh::lean_inc_ref(v_val_2263_);
            crate::leanh::lean_dec(v_t_2253_);
            v___x_2264_ = crate::leanh::lean_apply_1(v_k_2254_, v_val_2263_);
            return v___x_2264_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_ctorElim(
    mut v_motive_2265_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2266_: *mut crate::leanh::LeanObject,
    mut v_t_2267_: *mut crate::leanh::LeanObject,
    mut v_h_2268_: *mut crate::leanh::LeanObject,
    mut v_k_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2270_ = l_Lean_Declaration_ctorElim___redArg(v_t_2267_, v_k_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Lean_Declaration_ctorElim___boxed(
    mut v_motive_2271_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2272_: *mut crate::leanh::LeanObject,
    mut v_t_2273_: *mut crate::leanh::LeanObject,
    mut v_h_2274_: *mut crate::leanh::LeanObject,
    mut v_k_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Lean_Declaration_ctorElim(
        v_motive_2271_,
        v_ctorIdx_2272_,
        v_t_2273_,
        v_h_2274_,
        v_k_2275_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2272_);
    return v_res_2276_;
}
pub unsafe fn l_Lean_Declaration_axiomDecl_elim___redArg(
    mut v_t_2277_: *mut crate::leanh::LeanObject,
    mut v_axiomDecl_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2279_ = l_Lean_Declaration_ctorElim___redArg(v_t_2277_, v_axiomDecl_2278_);
    return v___x_2279_;
}
pub unsafe fn l_Lean_Declaration_axiomDecl_elim(
    mut v_motive_2280_: *mut crate::leanh::LeanObject,
    mut v_t_2281_: *mut crate::leanh::LeanObject,
    mut v_h_2282_: *mut crate::leanh::LeanObject,
    mut v_axiomDecl_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2284_ = l_Lean_Declaration_ctorElim___redArg(v_t_2281_, v_axiomDecl_2283_);
    return v___x_2284_;
}
pub unsafe fn l_Lean_Declaration_defnDecl_elim___redArg(
    mut v_t_2285_: *mut crate::leanh::LeanObject,
    mut v_defnDecl_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2287_ = l_Lean_Declaration_ctorElim___redArg(v_t_2285_, v_defnDecl_2286_);
    return v___x_2287_;
}
pub unsafe fn l_Lean_Declaration_defnDecl_elim(
    mut v_motive_2288_: *mut crate::leanh::LeanObject,
    mut v_t_2289_: *mut crate::leanh::LeanObject,
    mut v_h_2290_: *mut crate::leanh::LeanObject,
    mut v_defnDecl_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ = l_Lean_Declaration_ctorElim___redArg(v_t_2289_, v_defnDecl_2291_);
    return v___x_2292_;
}
pub unsafe fn l_Lean_Declaration_thmDecl_elim___redArg(
    mut v_t_2293_: *mut crate::leanh::LeanObject,
    mut v_thmDecl_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ = l_Lean_Declaration_ctorElim___redArg(v_t_2293_, v_thmDecl_2294_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_Declaration_thmDecl_elim(
    mut v_motive_2296_: *mut crate::leanh::LeanObject,
    mut v_t_2297_: *mut crate::leanh::LeanObject,
    mut v_h_2298_: *mut crate::leanh::LeanObject,
    mut v_thmDecl_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = l_Lean_Declaration_ctorElim___redArg(v_t_2297_, v_thmDecl_2299_);
    return v___x_2300_;
}
pub unsafe fn l_Lean_Declaration_opaqueDecl_elim___redArg(
    mut v_t_2301_: *mut crate::leanh::LeanObject,
    mut v_opaqueDecl_2302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2303_ = l_Lean_Declaration_ctorElim___redArg(v_t_2301_, v_opaqueDecl_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_Declaration_opaqueDecl_elim(
    mut v_motive_2304_: *mut crate::leanh::LeanObject,
    mut v_t_2305_: *mut crate::leanh::LeanObject,
    mut v_h_2306_: *mut crate::leanh::LeanObject,
    mut v_opaqueDecl_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = l_Lean_Declaration_ctorElim___redArg(v_t_2305_, v_opaqueDecl_2307_);
    return v___x_2308_;
}
pub unsafe fn l_Lean_Declaration_quotDecl_elim___redArg(
    mut v_t_2309_: *mut crate::leanh::LeanObject,
    mut v_quotDecl_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2311_ = l_Lean_Declaration_ctorElim___redArg(v_t_2309_, v_quotDecl_2310_);
    return v___x_2311_;
}
pub unsafe fn l_Lean_Declaration_quotDecl_elim(
    mut v_motive_2312_: *mut crate::leanh::LeanObject,
    mut v_t_2313_: *mut crate::leanh::LeanObject,
    mut v_h_2314_: *mut crate::leanh::LeanObject,
    mut v_quotDecl_2315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2316_ = l_Lean_Declaration_ctorElim___redArg(v_t_2313_, v_quotDecl_2315_);
    return v___x_2316_;
}
pub unsafe fn l_Lean_Declaration_mutualDefnDecl_elim___redArg(
    mut v_t_2317_: *mut crate::leanh::LeanObject,
    mut v_mutualDefnDecl_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_Lean_Declaration_ctorElim___redArg(v_t_2317_, v_mutualDefnDecl_2318_);
    return v___x_2319_;
}
pub unsafe fn l_Lean_Declaration_mutualDefnDecl_elim(
    mut v_motive_2320_: *mut crate::leanh::LeanObject,
    mut v_t_2321_: *mut crate::leanh::LeanObject,
    mut v_h_2322_: *mut crate::leanh::LeanObject,
    mut v_mutualDefnDecl_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2324_ = l_Lean_Declaration_ctorElim___redArg(v_t_2321_, v_mutualDefnDecl_2323_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_Declaration_inductDecl_elim___redArg(
    mut v_t_2325_: *mut crate::leanh::LeanObject,
    mut v_inductDecl_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Lean_Declaration_ctorElim___redArg(v_t_2325_, v_inductDecl_2326_);
    return v___x_2327_;
}
pub unsafe fn l_Lean_Declaration_inductDecl_elim(
    mut v_motive_2328_: *mut crate::leanh::LeanObject,
    mut v_t_2329_: *mut crate::leanh::LeanObject,
    mut v_h_2330_: *mut crate::leanh::LeanObject,
    mut v_inductDecl_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = l_Lean_Declaration_ctorElim___redArg(v_t_2329_, v_inductDecl_2331_);
    return v___x_2332_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclaration_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lean_instInhabitedAxiomVal_default;
    v___x_2334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2334_, 0, v___x_2333_);
    return v___x_2334_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclaration_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclaration_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedDeclaration_default___closed__0_once),
        _init_l_Lean_instInhabitedDeclaration_default___closed__0,
    );
    return v___x_2335_;
}
pub unsafe fn _init_l_Lean_instInhabitedDeclaration() -> *mut crate::leanh::LeanObject {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Lean_instInhabitedDeclaration_default;
    return v___x_2336_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(
    mut v_x_2337_: *mut crate::leanh::LeanObject,
    mut v_x_2338_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2339_: u8 = 0;
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: u8 = 0;
    let mut v_head_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2337_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_2338_) == 0 {
                        v___x_2339_ = 1;
                        return v___x_2339_;
                    } else {
                        v___x_2340_ = 0;
                        return v___x_2340_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_2338_) == 0 {
                        v___x_2341_ = 0;
                        return v___x_2341_;
                    } else {
                        v_head_2342_ = crate::leanh::lean_ctor_get(v_x_2337_, 0);
                        v_tail_2343_ = crate::leanh::lean_ctor_get(v_x_2337_, 1);
                        v_head_2344_ = crate::leanh::lean_ctor_get(v_x_2338_, 0);
                        v_tail_2345_ = crate::leanh::lean_ctor_get(v_x_2338_, 1);
                        v___x_2346_ = l_Lean_instBEqDefinitionVal_beq(v_head_2342_, v_head_2344_);
                        if v___x_2346_ == 0 {
                            return v___x_2346_;
                        } else {
                            v_x_2337_ = v_tail_2343_;
                            v_x_2338_ = v_tail_2345_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(
    mut v_x_2348_: *mut crate::leanh::LeanObject,
    mut v_x_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2350_: u8 = 0;
    let mut v_r_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2350_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_2348_, v_x_2349_);
    crate::leanh::lean_dec(v_x_2349_);
    crate::leanh::lean_dec(v_x_2348_);
    v_r_2351_ = crate::leanh::lean_box((v_res_2350_) as usize);
    return v_r_2351_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(
    mut v_x_2352_: *mut crate::leanh::LeanObject,
    mut v_x_2353_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: u8 = 0;
    let mut v_head_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2352_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_2353_) == 0 {
                        v___x_2354_ = 1;
                        return v___x_2354_;
                    } else {
                        v___x_2355_ = 0;
                        return v___x_2355_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_2353_) == 0 {
                        v___x_2356_ = 0;
                        return v___x_2356_;
                    } else {
                        v_head_2357_ = crate::leanh::lean_ctor_get(v_x_2352_, 0);
                        v_tail_2358_ = crate::leanh::lean_ctor_get(v_x_2352_, 1);
                        v_head_2359_ = crate::leanh::lean_ctor_get(v_x_2353_, 0);
                        v_tail_2360_ = crate::leanh::lean_ctor_get(v_x_2353_, 1);
                        v___x_2361_ = l_Lean_instBEqInductiveType_beq(v_head_2357_, v_head_2359_);
                        if v___x_2361_ == 0 {
                            return v___x_2361_;
                        } else {
                            v_x_2352_ = v_tail_2358_;
                            v_x_2353_ = v_tail_2360_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(
    mut v_x_2363_: *mut crate::leanh::LeanObject,
    mut v_x_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2365_: u8 = 0;
    let mut v_r_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2365_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_2363_, v_x_2364_);
    crate::leanh::lean_dec(v_x_2364_);
    crate::leanh::lean_dec(v_x_2363_);
    v_r_2366_ = crate::leanh::lean_box((v_res_2365_) as usize);
    return v_r_2366_;
}
pub unsafe fn l_Lean_instBEqDeclaration_beq(
    mut v_x_2367_: *mut crate::leanh::LeanObject,
    mut v_x_2368_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_2367_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_2368_) == 0 {
                let mut v_val_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_val_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2371_: u8 = 0;
                v_val_2369_ = crate::leanh::lean_ctor_get(v_x_2367_, 0);
                v_val_2370_ = crate::leanh::lean_ctor_get(v_x_2368_, 0);
                v___x_2371_ = l_Lean_instBEqAxiomVal_beq(v_val_2369_, v_val_2370_);
                return v___x_2371_;
            } else {
                let mut v___x_2372_: u8 = 0;
                v___x_2372_ = 0;
                return v___x_2372_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_2368_) == 1 {
                let mut v_val_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_val_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2375_: u8 = 0;
                v_val_2373_ = crate::leanh::lean_ctor_get(v_x_2367_, 0);
                v_val_2374_ = crate::leanh::lean_ctor_get(v_x_2368_, 0);
                v___x_2375_ = l_Lean_instBEqDefinitionVal_beq(v_val_2373_, v_val_2374_);
                return v___x_2375_;
            } else {
                let mut v___x_2376_: u8 = 0;
                v___x_2376_ = 0;
                return v___x_2376_;
            }
        }
        2 => {
            if crate::leanh::lean_obj_tag(v_x_2368_) == 2 {
                let mut v_val_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_val_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2379_: u8 = 0;
                v_val_2377_ = crate::leanh::lean_ctor_get(v_x_2367_, 0);
                v_val_2378_ = crate::leanh::lean_ctor_get(v_x_2368_, 0);
                v___x_2379_ = l_Lean_instBEqTheoremVal_beq(v_val_2377_, v_val_2378_);
                return v___x_2379_;
            } else {
                let mut v___x_2380_: u8 = 0;
                v___x_2380_ = 0;
                return v___x_2380_;
            }
        }
        3 => {
            if crate::leanh::lean_obj_tag(v_x_2368_) == 3 {
                let mut v_val_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_val_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2383_: u8 = 0;
                v_val_2381_ = crate::leanh::lean_ctor_get(v_x_2367_, 0);
                v_val_2382_ = crate::leanh::lean_ctor_get(v_x_2368_, 0);
                v___x_2383_ = l_Lean_instBEqOpaqueVal_beq(v_val_2381_, v_val_2382_);
                return v___x_2383_;
            } else {
                let mut v___x_2384_: u8 = 0;
                v___x_2384_ = 0;
                return v___x_2384_;
            }
        }
        4 => {
            if crate::leanh::lean_obj_tag(v_x_2368_) == 4 {
                let mut v___x_2385_: u8 = 0;
                v___x_2385_ = 1;
                return v___x_2385_;
            } else {
                let mut v___x_2386_: u8 = 0;
                v___x_2386_ = 0;
                return v___x_2386_;
            }
        }
        5 => {
            if crate::leanh::lean_obj_tag(v_x_2368_) == 5 {
                let mut v_defns_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_defns_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2389_: u8 = 0;
                v_defns_2387_ = crate::leanh::lean_ctor_get(v_x_2367_, 0);
                v_defns_2388_ = crate::leanh::lean_ctor_get(v_x_2368_, 0);
                v___x_2389_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(
                    v_defns_2387_,
                    v_defns_2388_,
                );
                return v___x_2389_;
            } else {
                let mut v___x_2390_: u8 = 0;
                v___x_2390_ = 0;
                return v___x_2390_;
            }
        }
        _ => {
            if crate::leanh::lean_obj_tag(v_x_2368_) == 6 {
                let mut v_lparams_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_nparams_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_types_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_isUnsafe_2394_: u8 = 0;
                let mut v_lparams_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_nparams_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_types_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_isUnsafe_2398_: u8 = 0;
                let mut v___x_2399_: u8 = 0;
                v_lparams_2391_ = crate::leanh::lean_ctor_get(v_x_2367_, 0);
                v_nparams_2392_ = crate::leanh::lean_ctor_get(v_x_2367_, 1);
                v_types_2393_ = crate::leanh::lean_ctor_get(v_x_2367_, 2);
                v_isUnsafe_2394_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2367_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_lparams_2395_ = crate::leanh::lean_ctor_get(v_x_2368_, 0);
                v_nparams_2396_ = crate::leanh::lean_ctor_get(v_x_2368_, 1);
                v_types_2397_ = crate::leanh::lean_ctor_get(v_x_2368_, 2);
                v_isUnsafe_2398_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2368_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_2399_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(
                    v_lparams_2391_,
                    v_lparams_2395_,
                );
                if v___x_2399_ == 0 {
                    return v___x_2399_;
                } else {
                    let mut v___x_2400_: u8 = 0;
                    v___x_2400_ = lean_nat_dec_eq(v_nparams_2392_, v_nparams_2396_);
                    if v___x_2400_ == 0 {
                        return v___x_2400_;
                    } else {
                        let mut v___x_2401_: u8 = 0;
                        v___x_2401_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(
                            v_types_2393_,
                            v_types_2397_,
                        );
                        if v___x_2401_ == 0 {
                            return v___x_2401_;
                        } else {
                            if v_isUnsafe_2394_ == 0 {
                                if v_isUnsafe_2398_ == 0 {
                                    return v___x_2401_;
                                } else {
                                    return v_isUnsafe_2394_;
                                }
                            } else {
                                return v_isUnsafe_2398_;
                            }
                        }
                    }
                }
            } else {
                let mut v___x_2402_: u8 = 0;
                v___x_2402_ = 0;
                return v___x_2402_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqDeclaration_beq___boxed(
    mut v_x_2403_: *mut crate::leanh::LeanObject,
    mut v_x_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2405_: u8 = 0;
    let mut v_r_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2405_ = l_Lean_instBEqDeclaration_beq(v_x_2403_, v_x_2404_);
    crate::leanh::lean_dec(v_x_2404_);
    crate::leanh::lean_dec(v_x_2403_);
    v_r_2406_ = crate::leanh::lean_box((v_res_2405_) as usize);
    return v_r_2406_;
}
pub unsafe fn lean_mk_inductive_decl(
    mut v_lparams_2409_: *mut crate::leanh::LeanObject,
    mut v_nparams_2410_: *mut crate::leanh::LeanObject,
    mut v_types_2411_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2412_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = crate::leanh::lean_alloc_ctor(6, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2413_, 0, v_lparams_2409_);
    crate::leanh::lean_ctor_set(v___x_2413_, 1, v_nparams_2410_);
    crate::leanh::lean_ctor_set(v___x_2413_, 2, v_types_2411_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2413_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_isUnsafe_2412_,
    );
    return v___x_2413_;
}
pub unsafe fn l_Lean_mkInductiveDeclEs___boxed(
    mut v_lparams_2414_: *mut crate::leanh::LeanObject,
    mut v_nparams_2415_: *mut crate::leanh::LeanObject,
    mut v_types_2416_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isUnsafe_boxed_2418_: u8 = 0;
    let mut v_res_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isUnsafe_boxed_2418_ = (crate::leanh::lean_unbox(v_isUnsafe_2417_) as u8);
    v_res_2419_ = lean_mk_inductive_decl(
        v_lparams_2414_,
        v_nparams_2415_,
        v_types_2416_,
        v_isUnsafe_boxed_2418_,
    );
    return v_res_2419_;
}
pub unsafe fn lean_is_unsafe_inductive_decl(mut v_x_2420_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2420_) == 6 {
        let mut v_isUnsafe_2421_: u8 = 0;
        v_isUnsafe_2421_ = crate::leanh::lean_ctor_get_uint8(
            v_x_2420_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_x_2420_, 3);
        return v_isUnsafe_2421_;
    } else {
        let mut v___x_2422_: u8 = 0;
        crate::leanh::lean_dec(v_x_2420_);
        v___x_2422_ = 0;
        return v___x_2422_;
    }
}
pub unsafe fn l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(
    mut v_x_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2424_: u8 = 0;
    let mut v_r_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = lean_is_unsafe_inductive_decl(v_x_2423_);
    v_r_2425_ = crate::leanh::lean_box((v_res_2424_) as usize);
    return v_r_2425_;
}
pub unsafe fn l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(
    mut v_msg_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lean_instInhabitedDefinitionVal_default;
    v___x_2428_ = lean_panic_fn_borrowed(v___x_2427_, v_msg_2426_);
    return v___x_2428_;
}
pub unsafe fn _init_l_Lean_Declaration_definitionVal_x21___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = l_Lean_Declaration_definitionVal_x21___closed__2;
    v___x_2433_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_2434_ = crate::leanh::lean_unsigned_to_nat(206);
    v___x_2435_ = l_Lean_Declaration_definitionVal_x21___closed__1;
    v___x_2436_ = l_Lean_Declaration_definitionVal_x21___closed__0;
    v___x_2437_ = l_mkPanicMessageWithDecl(
        v___x_2436_,
        v___x_2435_,
        v___x_2434_,
        v___x_2433_,
        v___x_2432_,
    );
    return v___x_2437_;
}
pub unsafe fn l_Lean_Declaration_definitionVal_x21(
    mut v_x_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2438_) == 1 {
        let mut v_val_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2439_ = crate::leanh::lean_ctor_get(v_x_2438_, 0);
        crate::leanh::lean_inc_ref(v_val_2439_);
        return v_val_2439_;
    } else {
        let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2440_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Declaration_definitionVal_x21___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Declaration_definitionVal_x21___closed__3_once),
            _init_l_Lean_Declaration_definitionVal_x21___closed__3,
        );
        v___x_2441_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_2440_);
        return v___x_2441_;
    }
}
pub unsafe fn l_Lean_Declaration_definitionVal_x21___boxed(
    mut v_x_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Lean_Declaration_definitionVal_x21(v_x_2442_);
    crate::leanh::lean_dec(v_x_2442_);
    return v_res_2443_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2452_: u8 = 0;
    let mut v_name_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v_unused_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2444_) == 0 {
                    v___x_2446_ = l_List_reverse___redArg(v_a_2445_);
                    return v___x_2446_;
                } else {
                    v_head_2447_ = crate::leanh::lean_ctor_get(v_a_2444_, 0);
                    v_toConstantVal_2448_ = crate::leanh::lean_ctor_get(v_head_2447_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_2448_);
                    v_tail_2449_ = crate::leanh::lean_ctor_get(v_a_2444_, 1);
                    v_isSharedCheck_2458_ = (!crate::leanh::lean_is_exclusive(v_a_2444_)) as u8;
                    if v_isSharedCheck_2458_ == 0 {
                        v_unused_2459_ = crate::leanh::lean_ctor_get(v_a_2444_, 0);
                        crate::leanh::lean_dec(v_unused_2459_);
                        v___x_2451_ = v_a_2444_;
                        v_isShared_2452_ = v_isSharedCheck_2458_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2449_);
                        crate::leanh::lean_dec(v_a_2444_);
                        v___x_2451_ = crate::leanh::lean_box(0);
                        v_isShared_2452_ = v_isSharedCheck_2458_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_2453_ = crate::leanh::lean_ctor_get(v_toConstantVal_2448_, 0);
                crate::leanh::lean_inc(v_name_2453_);
                crate::leanh::lean_dec_ref(v_toConstantVal_2448_);
                if v_isShared_2452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2451_, 1, v_a_2445_);
                    crate::leanh::lean_ctor_set(v___x_2451_, 0, v_name_2453_);
                    v___x_2455_ = v___x_2451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_name_2453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_a_2445_);
                    v___x_2455_ = v_reuseFailAlloc_2457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2444_ = v_tail_2449_;
                v_a_2445_ = v___x_2455_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v_name_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2460_) == 0 {
                    v___x_2462_ = l_List_reverse___redArg(v_a_2461_);
                    return v___x_2462_;
                } else {
                    v_head_2463_ = crate::leanh::lean_ctor_get(v_a_2460_, 0);
                    v_tail_2464_ = crate::leanh::lean_ctor_get(v_a_2460_, 1);
                    v_isSharedCheck_2473_ = (!crate::leanh::lean_is_exclusive(v_a_2460_)) as u8;
                    if v_isSharedCheck_2473_ == 0 {
                        v___x_2466_ = v_a_2460_;
                        v_isShared_2467_ = v_isSharedCheck_2473_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2464_);
                        crate::leanh::lean_inc(v_head_2463_);
                        crate::leanh::lean_dec(v_a_2460_);
                        v___x_2466_ = crate::leanh::lean_box(0);
                        v_isShared_2467_ = v_isSharedCheck_2473_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_2468_ = crate::leanh::lean_ctor_get(v_head_2463_, 0);
                crate::leanh::lean_inc(v_name_2468_);
                crate::leanh::lean_dec(v_head_2463_);
                if v_isShared_2467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2466_, 1, v_a_2461_);
                    crate::leanh::lean_ctor_set(v___x_2466_, 0, v_name_2468_);
                    v___x_2470_ = v___x_2466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_name_2468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_a_2461_);
                    v___x_2470_ = v_reuseFailAlloc_2472_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2460_ = v_tail_2464_;
                v_a_2461_ = v___x_2470_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Declaration_getTopLevelNames(
    mut v_x_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2480_) {
        4 => {
            let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2481_ = l_Lean_Declaration_getTopLevelNames___closed__2;
            return v___x_2481_;
        }
        5 => {
            let mut v_defns_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_defns_2482_ = crate::leanh::lean_ctor_get(v_x_2480_, 0);
            crate::leanh::lean_inc(v_defns_2482_);
            crate::leanh::lean_dec_ref_known(v_x_2480_, 1);
            v___x_2483_ = crate::leanh::lean_box(0);
            v___x_2484_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(
                v_defns_2482_,
                v___x_2483_,
            );
            return v___x_2484_;
        }
        6 => {
            let mut v_types_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_types_2485_ = crate::leanh::lean_ctor_get(v_x_2480_, 2);
            crate::leanh::lean_inc(v_types_2485_);
            crate::leanh::lean_dec_ref_known(v_x_2480_, 3);
            v___x_2486_ = crate::leanh::lean_box(0);
            v___x_2487_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(
                v_types_2485_,
                v___x_2486_,
            );
            return v___x_2487_;
        }
        _ => {
            let mut v_val_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2488_ = crate::leanh::lean_ctor_get(v_x_2480_, 0);
            crate::leanh::lean_inc_ref(v_val_2488_);
            crate::leanh::lean_dec(v_x_2480_);
            v_toConstantVal_2489_ = crate::leanh::lean_ctor_get(v_val_2488_, 0);
            crate::leanh::lean_inc_ref(v_toConstantVal_2489_);
            crate::leanh::lean_dec_ref(v_val_2488_);
            v_name_2490_ = crate::leanh::lean_ctor_get(v_toConstantVal_2489_, 0);
            crate::leanh::lean_inc(v_name_2490_);
            crate::leanh::lean_dec_ref(v_toConstantVal_2489_);
            v___x_2491_ = crate::leanh::lean_box(0);
            v___x_2492_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2492_, 0, v_name_2490_);
            crate::leanh::lean_ctor_set(v___x_2492_, 1, v___x_2491_);
            return v___x_2492_;
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(
    mut v_a_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v_name_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2493_) == 0 {
                    v___x_2495_ = l_List_reverse___redArg(v_a_2494_);
                    return v___x_2495_;
                } else {
                    v_head_2496_ = crate::leanh::lean_ctor_get(v_a_2493_, 0);
                    v_tail_2497_ = crate::leanh::lean_ctor_get(v_a_2493_, 1);
                    v_isSharedCheck_2506_ = (!crate::leanh::lean_is_exclusive(v_a_2493_)) as u8;
                    if v_isSharedCheck_2506_ == 0 {
                        v___x_2499_ = v_a_2493_;
                        v_isShared_2500_ = v_isSharedCheck_2506_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2497_);
                        crate::leanh::lean_inc(v_head_2496_);
                        crate::leanh::lean_dec(v_a_2493_);
                        v___x_2499_ = crate::leanh::lean_box(0);
                        v_isShared_2500_ = v_isSharedCheck_2506_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_2501_ = crate::leanh::lean_ctor_get(v_head_2496_, 0);
                crate::leanh::lean_inc(v_name_2501_);
                crate::leanh::lean_dec(v_head_2496_);
                if v_isShared_2500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2499_, 1, v_a_2494_);
                    crate::leanh::lean_ctor_set(v___x_2499_, 0, v_name_2501_);
                    v___x_2503_ = v___x_2499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_name_2501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_a_2494_);
                    v___x_2503_ = v_reuseFailAlloc_2505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2493_ = v_tail_2497_;
                v_a_2494_ = v___x_2503_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v_name_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2510_) == 0 {
                    v___x_2512_ = lean_array_to_list(v_a_2511_);
                    return v___x_2512_;
                } else {
                    v_head_2513_ = crate::leanh::lean_ctor_get(v_a_2510_, 0);
                    v_tail_2514_ = crate::leanh::lean_ctor_get(v_a_2510_, 1);
                    v_isSharedCheck_2530_ = (!crate::leanh::lean_is_exclusive(v_a_2510_)) as u8;
                    if v_isSharedCheck_2530_ == 0 {
                        v___x_2516_ = v_a_2510_;
                        v_isShared_2517_ = v_isSharedCheck_2530_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2514_);
                        crate::leanh::lean_inc(v_head_2513_);
                        crate::leanh::lean_dec(v_a_2510_);
                        v___x_2516_ = crate::leanh::lean_box(0);
                        v_isShared_2517_ = v_isSharedCheck_2530_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_2518_ = crate::leanh::lean_ctor_get(v_head_2513_, 0);
                crate::leanh::lean_inc(v_name_2518_);
                v_ctors_2519_ = crate::leanh::lean_ctor_get(v_head_2513_, 2);
                crate::leanh::lean_inc(v_ctors_2519_);
                crate::leanh::lean_dec(v_head_2513_);
                v___x_2520_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1;
                v___x_2521_ = l_Lean_Name_appendCore(v_name_2518_, v___x_2520_);
                v___x_2522_ = crate::leanh::lean_box(0);
                v___x_2523_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(
                    v_ctors_2519_,
                    v___x_2522_,
                );
                if v_isShared_2517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2516_, 1, v___x_2523_);
                    crate::leanh::lean_ctor_set(v___x_2516_, 0, v___x_2521_);
                    v___x_2525_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2523_);
                    v___x_2525_ = v_reuseFailAlloc_2529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2526_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2526_, 0, v_name_2518_);
                crate::leanh::lean_ctor_set(v___x_2526_, 1, v___x_2525_);
                v___x_2527_ =
                    l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2511_, v___x_2526_);
                v_a_2510_ = v_tail_2514_;
                v_a_2511_ = v___x_2527_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Declaration_getNames(
    mut v_x_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2557_) {
        4 => {
            let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2558_ = l_Lean_Declaration_getNames___closed__9;
            return v___x_2558_;
        }
        5 => {
            let mut v_defns_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_defns_2559_ = crate::leanh::lean_ctor_get(v_x_2557_, 0);
            crate::leanh::lean_inc(v_defns_2559_);
            crate::leanh::lean_dec_ref_known(v_x_2557_, 1);
            v___x_2560_ = crate::leanh::lean_box(0);
            v___x_2561_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(
                v_defns_2559_,
                v___x_2560_,
            );
            return v___x_2561_;
        }
        6 => {
            let mut v_types_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_types_2562_ = crate::leanh::lean_ctor_get(v_x_2557_, 2);
            crate::leanh::lean_inc(v_types_2562_);
            crate::leanh::lean_dec_ref_known(v_x_2557_, 3);
            v___x_2563_ = l_Lean_Declaration_getNames___closed__10;
            v___x_2564_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_2562_, v___x_2563_);
            return v___x_2564_;
        }
        _ => {
            let mut v_val_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_name_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2565_ = crate::leanh::lean_ctor_get(v_x_2557_, 0);
            crate::leanh::lean_inc_ref(v_val_2565_);
            crate::leanh::lean_dec(v_x_2557_);
            v_toConstantVal_2566_ = crate::leanh::lean_ctor_get(v_val_2565_, 0);
            crate::leanh::lean_inc_ref(v_toConstantVal_2566_);
            crate::leanh::lean_dec_ref(v_val_2565_);
            v_name_2567_ = crate::leanh::lean_ctor_get(v_toConstantVal_2566_, 0);
            crate::leanh::lean_inc(v_name_2567_);
            crate::leanh::lean_dec_ref(v_toConstantVal_2566_);
            v___x_2568_ = crate::leanh::lean_box(0);
            v___x_2569_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2569_, 0, v_name_2567_);
            crate::leanh::lean_ctor_set(v___x_2569_, 1, v___x_2568_);
            return v___x_2569_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___redArg___lam__0(
    mut v_f_2570_: *mut crate::leanh::LeanObject,
    mut v_value_2571_: *mut crate::leanh::LeanObject,
    mut v_a_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = crate::leanh::lean_apply_2(v_f_2570_, v_a_2572_, v_value_2571_);
    return v___x_2573_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___redArg___lam__3(
    mut v_f_2574_: *mut crate::leanh::LeanObject,
    mut v_value_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2577_ = crate::leanh::lean_apply_2(v_f_2574_, v_a_2576_, v_value_2575_);
    return v___x_2577_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___redArg___lam__1(
    mut v_f_2578_: *mut crate::leanh::LeanObject,
    mut v_toBind_2579_: *mut crate::leanh::LeanObject,
    mut v_a_2580_: *mut crate::leanh::LeanObject,
    mut v_v_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toConstantVal_2582_ = crate::leanh::lean_ctor_get(v_v_2581_, 0);
    crate::leanh::lean_inc_ref(v_toConstantVal_2582_);
    v_value_2583_ = crate::leanh::lean_ctor_get(v_v_2581_, 1);
    crate::leanh::lean_inc_ref(v_value_2583_);
    crate::leanh::lean_dec_ref(v_v_2581_);
    v_type_2584_ = crate::leanh::lean_ctor_get(v_toConstantVal_2582_, 2);
    crate::leanh::lean_inc_ref(v_type_2584_);
    crate::leanh::lean_dec_ref(v_toConstantVal_2582_);
    crate::leanh::lean_inc(v_f_2578_);
    v___f_2585_ = crate::leanh::lean_alloc_closure(
        l_Lean_Declaration_foldExprM___redArg___lam__3 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2585_, 0, v_f_2578_);
    crate::leanh::lean_closure_set(v___f_2585_, 1, v_value_2583_);
    v___x_2586_ = crate::leanh::lean_apply_2(v_f_2578_, v_a_2580_, v_type_2584_);
    v___x_2587_ = crate::leanh::lean_apply_4(
        v_toBind_2579_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2586_,
        v___f_2585_,
    );
    return v___x_2587_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___redArg___lam__2(
    mut v_f_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
    mut v_ctor_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_2591_ = crate::leanh::lean_ctor_get(v_ctor_2590_, 1);
    crate::leanh::lean_inc_ref(v_type_2591_);
    crate::leanh::lean_dec_ref(v_ctor_2590_);
    v___x_2592_ = crate::leanh::lean_apply_2(v_f_2588_, v_a_2589_, v_type_2591_);
    return v___x_2592_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___redArg___lam__4(
    mut v_inst_2593_: *mut crate::leanh::LeanObject,
    mut v___f_2594_: *mut crate::leanh::LeanObject,
    mut v_ctors_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2597_ = l_List_foldlM___redArg(v_inst_2593_, v___f_2594_, v_a_2596_, v_ctors_2595_);
    return v___x_2597_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___redArg___lam__5(
    mut v_inst_2598_: *mut crate::leanh::LeanObject,
    mut v___f_2599_: *mut crate::leanh::LeanObject,
    mut v_f_2600_: *mut crate::leanh::LeanObject,
    mut v_toBind_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v_inductType_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_2604_ = crate::leanh::lean_ctor_get(v_inductType_2603_, 1);
    crate::leanh::lean_inc_ref(v_type_2604_);
    v_ctors_2605_ = crate::leanh::lean_ctor_get(v_inductType_2603_, 2);
    crate::leanh::lean_inc(v_ctors_2605_);
    crate::leanh::lean_dec_ref(v_inductType_2603_);
    v___f_2606_ = crate::leanh::lean_alloc_closure(
        l_Lean_Declaration_foldExprM___redArg___lam__4 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2606_, 0, v_inst_2598_);
    crate::leanh::lean_closure_set(v___f_2606_, 1, v___f_2599_);
    crate::leanh::lean_closure_set(v___f_2606_, 2, v_ctors_2605_);
    v___x_2607_ = crate::leanh::lean_apply_2(v_f_2600_, v_a_2602_, v_type_2604_);
    v___x_2608_ = crate::leanh::lean_apply_4(
        v_toBind_2601_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2607_,
        v___f_2606_,
    );
    return v___x_2608_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___redArg(
    mut v_inst_2609_: *mut crate::leanh::LeanObject,
    mut v_d_2610_: *mut crate::leanh::LeanObject,
    mut v_f_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_d_2610_) {
        0 => {
            let mut v_val_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_2609_);
            v_val_2613_ = crate::leanh::lean_ctor_get(v_d_2610_, 0);
            crate::leanh::lean_inc_ref(v_val_2613_);
            crate::leanh::lean_dec_ref_known(v_d_2610_, 1);
            v_toConstantVal_2614_ = crate::leanh::lean_ctor_get(v_val_2613_, 0);
            crate::leanh::lean_inc_ref(v_toConstantVal_2614_);
            crate::leanh::lean_dec_ref(v_val_2613_);
            v_type_2615_ = crate::leanh::lean_ctor_get(v_toConstantVal_2614_, 2);
            crate::leanh::lean_inc_ref(v_type_2615_);
            crate::leanh::lean_dec_ref(v_toConstantVal_2614_);
            v___x_2616_ = crate::leanh::lean_apply_2(v_f_2611_, v_a_2612_, v_type_2615_);
            return v___x_2616_;
        }
        4 => {
            let mut v_toApplicative_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_2617_ = crate::leanh::lean_ctor_get(v_inst_2609_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_2617_);
            crate::leanh::lean_dec(v_f_2611_);
            crate::leanh::lean_dec_ref(v_inst_2609_);
            v_toPure_2618_ = crate::leanh::lean_ctor_get(v_toApplicative_2617_, 1);
            crate::leanh::lean_inc(v_toPure_2618_);
            crate::leanh::lean_dec_ref(v_toApplicative_2617_);
            v___x_2619_ =
                crate::leanh::lean_apply_2(v_toPure_2618_, crate::leanh::lean_box(0), v_a_2612_);
            return v___x_2619_;
        }
        5 => {
            let mut v_toBind_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_defns_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_2620_ = crate::leanh::lean_ctor_get(v_inst_2609_, 1);
            v_defns_2621_ = crate::leanh::lean_ctor_get(v_d_2610_, 0);
            crate::leanh::lean_inc(v_defns_2621_);
            crate::leanh::lean_dec_ref_known(v_d_2610_, 1);
            crate::leanh::lean_inc(v_toBind_2620_);
            v___f_2622_ = crate::leanh::lean_alloc_closure(
                l_Lean_Declaration_foldExprM___redArg___lam__1 as *mut core::ffi::c_void,
                4,
                2,
            );
            crate::leanh::lean_closure_set(v___f_2622_, 0, v_f_2611_);
            crate::leanh::lean_closure_set(v___f_2622_, 1, v_toBind_2620_);
            v___x_2623_ =
                l_List_foldlM___redArg(v_inst_2609_, v___f_2622_, v_a_2612_, v_defns_2621_);
            return v___x_2623_;
        }
        6 => {
            let mut v_toBind_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_types_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_2624_ = crate::leanh::lean_ctor_get(v_inst_2609_, 1);
            v_types_2625_ = crate::leanh::lean_ctor_get(v_d_2610_, 2);
            crate::leanh::lean_inc(v_types_2625_);
            crate::leanh::lean_dec_ref_known(v_d_2610_, 3);
            crate::leanh::lean_inc(v_f_2611_);
            v___f_2626_ = crate::leanh::lean_alloc_closure(
                l_Lean_Declaration_foldExprM___redArg___lam__2 as *mut core::ffi::c_void,
                3,
                1,
            );
            crate::leanh::lean_closure_set(v___f_2626_, 0, v_f_2611_);
            crate::leanh::lean_inc(v_toBind_2624_);
            crate::leanh::lean_inc_ref(v_inst_2609_);
            v___f_2627_ = crate::leanh::lean_alloc_closure(
                l_Lean_Declaration_foldExprM___redArg___lam__5 as *mut core::ffi::c_void,
                6,
                4,
            );
            crate::leanh::lean_closure_set(v___f_2627_, 0, v_inst_2609_);
            crate::leanh::lean_closure_set(v___f_2627_, 1, v___f_2626_);
            crate::leanh::lean_closure_set(v___f_2627_, 2, v_f_2611_);
            crate::leanh::lean_closure_set(v___f_2627_, 3, v_toBind_2624_);
            v___x_2628_ =
                l_List_foldlM___redArg(v_inst_2609_, v___f_2627_, v_a_2612_, v_types_2625_);
            return v___x_2628_;
        }
        _ => {
            let mut v_val_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2629_ = crate::leanh::lean_ctor_get(v_d_2610_, 0);
            crate::leanh::lean_inc_ref(v_val_2629_);
            crate::leanh::lean_dec(v_d_2610_);
            v_toConstantVal_2630_ = crate::leanh::lean_ctor_get(v_val_2629_, 0);
            crate::leanh::lean_inc_ref(v_toConstantVal_2630_);
            v_toBind_2631_ = crate::leanh::lean_ctor_get(v_inst_2609_, 1);
            crate::leanh::lean_inc(v_toBind_2631_);
            crate::leanh::lean_dec_ref(v_inst_2609_);
            v_value_2632_ = crate::leanh::lean_ctor_get(v_val_2629_, 1);
            crate::leanh::lean_inc_ref(v_value_2632_);
            crate::leanh::lean_dec_ref(v_val_2629_);
            v_type_2633_ = crate::leanh::lean_ctor_get(v_toConstantVal_2630_, 2);
            crate::leanh::lean_inc_ref(v_type_2633_);
            crate::leanh::lean_dec_ref(v_toConstantVal_2630_);
            crate::leanh::lean_inc(v_f_2611_);
            v___f_2634_ = crate::leanh::lean_alloc_closure(
                l_Lean_Declaration_foldExprM___redArg___lam__0 as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_2634_, 0, v_f_2611_);
            crate::leanh::lean_closure_set(v___f_2634_, 1, v_value_2632_);
            v___x_2635_ = crate::leanh::lean_apply_2(v_f_2611_, v_a_2612_, v_type_2633_);
            v___x_2636_ = crate::leanh::lean_apply_4(
                v_toBind_2631_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_2635_,
                v___f_2634_,
            );
            return v___x_2636_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM(
    mut v_00_u03b1_2637_: *mut crate::leanh::LeanObject,
    mut v_m_2638_: *mut crate::leanh::LeanObject,
    mut v_inst_2639_: *mut crate::leanh::LeanObject,
    mut v_d_2640_: *mut crate::leanh::LeanObject,
    mut v_f_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2643_ =
        l_Lean_Declaration_foldExprM___redArg(v_inst_2639_, v_d_2640_, v_f_2641_, v_a_2642_);
    return v___x_2643_;
}
pub unsafe fn l_Lean_Declaration_forExprM___redArg___lam__0(
    mut v_f_2644_: *mut crate::leanh::LeanObject,
    mut v_x_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2647_ = crate::leanh::lean_apply_1(v_f_2644_, v_a_2646_);
    return v___x_2647_;
}
pub unsafe fn l_Lean_Declaration_forExprM___redArg(
    mut v_inst_2648_: *mut crate::leanh::LeanObject,
    mut v_d_2649_: *mut crate::leanh::LeanObject,
    mut v_f_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2651_ = crate::leanh::lean_alloc_closure(
        l_Lean_Declaration_forExprM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2651_, 0, v_f_2650_);
    v___x_2652_ = crate::leanh::lean_box(0);
    v___x_2653_ =
        l_Lean_Declaration_foldExprM___redArg(v_inst_2648_, v_d_2649_, v___f_2651_, v___x_2652_);
    return v___x_2653_;
}
pub unsafe fn l_Lean_Declaration_forExprM(
    mut v_m_2654_: *mut crate::leanh::LeanObject,
    mut v_inst_2655_: *mut crate::leanh::LeanObject,
    mut v_d_2656_: *mut crate::leanh::LeanObject,
    mut v_f_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2658_ = crate::leanh::lean_alloc_closure(
        l_Lean_Declaration_forExprM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2658_, 0, v_f_2657_);
    v___x_2659_ = crate::leanh::lean_box(0);
    v___x_2660_ =
        l_Lean_Declaration_foldExprM___redArg(v_inst_2655_, v_d_2656_, v___f_2658_, v___x_2659_);
    return v___x_2660_;
}
pub unsafe fn _init_l_Lean_instInhabitedInductiveVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2661_: u8 = 0;
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = 0;
    v___x_2662_ = crate::leanh::lean_box(0);
    v___x_2663_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2664_ = l_Lean_instInhabitedConstantVal_default;
    v___x_2665_ = crate::leanh::lean_alloc_ctor(0, 6, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_2665_, 0, v___x_2664_);
    crate::leanh::lean_ctor_set(v___x_2665_, 1, v___x_2663_);
    crate::leanh::lean_ctor_set(v___x_2665_, 2, v___x_2663_);
    crate::leanh::lean_ctor_set(v___x_2665_, 3, v___x_2662_);
    crate::leanh::lean_ctor_set(v___x_2665_, 4, v___x_2662_);
    crate::leanh::lean_ctor_set(v___x_2665_, 5, v___x_2663_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2665_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        v___x_2661_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2665_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 1) as u32,
        v___x_2661_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2665_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 2) as u32,
        v___x_2661_,
    );
    return v___x_2665_;
}
pub unsafe fn _init_l_Lean_instInhabitedInductiveVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2666_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedInductiveVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedInductiveVal_default___closed__0_once),
        _init_l_Lean_instInhabitedInductiveVal_default___closed__0,
    );
    return v___x_2666_;
}
pub unsafe fn _init_l_Lean_instInhabitedInductiveVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Lean_instInhabitedInductiveVal_default;
    return v___x_2667_;
}
pub unsafe fn lean_mk_inductive_val(
    mut v_name_2668_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2669_: *mut crate::leanh::LeanObject,
    mut v_type_2670_: *mut crate::leanh::LeanObject,
    mut v_numParams_2671_: *mut crate::leanh::LeanObject,
    mut v_numIndices_2672_: *mut crate::leanh::LeanObject,
    mut v_all_2673_: *mut crate::leanh::LeanObject,
    mut v_ctors_2674_: *mut crate::leanh::LeanObject,
    mut v_numNested_2675_: *mut crate::leanh::LeanObject,
    mut v_isRec_2676_: u8,
    mut v_isUnsafe_2677_: u8,
    mut v_isReflexive_2678_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2679_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2679_, 0, v_name_2668_);
    crate::leanh::lean_ctor_set(v___x_2679_, 1, v_levelParams_2669_);
    crate::leanh::lean_ctor_set(v___x_2679_, 2, v_type_2670_);
    v___x_2680_ = crate::leanh::lean_alloc_ctor(0, 6, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_2680_, 0, v___x_2679_);
    crate::leanh::lean_ctor_set(v___x_2680_, 1, v_numParams_2671_);
    crate::leanh::lean_ctor_set(v___x_2680_, 2, v_numIndices_2672_);
    crate::leanh::lean_ctor_set(v___x_2680_, 3, v_all_2673_);
    crate::leanh::lean_ctor_set(v___x_2680_, 4, v_ctors_2674_);
    crate::leanh::lean_ctor_set(v___x_2680_, 5, v_numNested_2675_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2680_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        v_isRec_2676_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2680_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 1) as u32,
        v_isUnsafe_2677_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2680_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 2) as u32,
        v_isReflexive_2678_,
    );
    return v___x_2680_;
}
pub unsafe fn l_Lean_mkInductiveValEx___boxed(
    mut v_name_2681_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2682_: *mut crate::leanh::LeanObject,
    mut v_type_2683_: *mut crate::leanh::LeanObject,
    mut v_numParams_2684_: *mut crate::leanh::LeanObject,
    mut v_numIndices_2685_: *mut crate::leanh::LeanObject,
    mut v_all_2686_: *mut crate::leanh::LeanObject,
    mut v_ctors_2687_: *mut crate::leanh::LeanObject,
    mut v_numNested_2688_: *mut crate::leanh::LeanObject,
    mut v_isRec_2689_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2690_: *mut crate::leanh::LeanObject,
    mut v_isReflexive_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isRec_boxed_2692_: u8 = 0;
    let mut v_isUnsafe_boxed_2693_: u8 = 0;
    let mut v_isReflexive_boxed_2694_: u8 = 0;
    let mut v_res_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isRec_boxed_2692_ = (crate::leanh::lean_unbox(v_isRec_2689_) as u8);
    v_isUnsafe_boxed_2693_ = (crate::leanh::lean_unbox(v_isUnsafe_2690_) as u8);
    v_isReflexive_boxed_2694_ = (crate::leanh::lean_unbox(v_isReflexive_2691_) as u8);
    v_res_2695_ = lean_mk_inductive_val(
        v_name_2681_,
        v_levelParams_2682_,
        v_type_2683_,
        v_numParams_2684_,
        v_numIndices_2685_,
        v_all_2686_,
        v_ctors_2687_,
        v_numNested_2688_,
        v_isRec_boxed_2692_,
        v_isUnsafe_boxed_2693_,
        v_isReflexive_boxed_2694_,
    );
    return v_res_2695_;
}
pub unsafe fn lean_inductive_val_is_rec(mut v_v_2696_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_isRec_2697_: u8 = 0;
    v_isRec_2697_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2696_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2696_);
    return v_isRec_2697_;
}
pub unsafe fn l_Lean_InductiveVal_isRecEx___boxed(
    mut v_v_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2699_: u8 = 0;
    let mut v_r_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2699_ = lean_inductive_val_is_rec(v_v_2698_);
    v_r_2700_ = crate::leanh::lean_box((v_res_2699_) as usize);
    return v_r_2700_;
}
pub unsafe fn lean_inductive_val_is_unsafe(mut v_v_2701_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_isUnsafe_2702_: u8 = 0;
    v_isUnsafe_2702_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2701_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 1) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2701_);
    return v_isUnsafe_2702_;
}
pub unsafe fn l_Lean_InductiveVal_isUnsafeEx___boxed(
    mut v_v_2703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2704_: u8 = 0;
    let mut v_r_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2704_ = lean_inductive_val_is_unsafe(v_v_2703_);
    v_r_2705_ = crate::leanh::lean_box((v_res_2704_) as usize);
    return v_r_2705_;
}
pub unsafe fn lean_inductive_val_is_reflexive(mut v_v_2706_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_isReflexive_2707_: u8 = 0;
    v_isReflexive_2707_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2706_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 2) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2706_);
    return v_isReflexive_2707_;
}
pub unsafe fn l_Lean_InductiveVal_isReflexiveEx___boxed(
    mut v_v_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2709_: u8 = 0;
    let mut v_r_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2709_ = lean_inductive_val_is_reflexive(v_v_2708_);
    v_r_2710_ = crate::leanh::lean_box((v_res_2709_) as usize);
    return v_r_2710_;
}
pub unsafe fn l_Lean_InductiveVal_numCtors(
    mut v_v_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctors_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ctors_2712_ = crate::leanh::lean_ctor_get(v_v_2711_, 4);
    v___x_2713_ = l_List_lengthTR___redArg(v_ctors_2712_);
    return v___x_2713_;
}
pub unsafe fn l_Lean_InductiveVal_numCtors___boxed(
    mut v_v_2714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2715_ = l_Lean_InductiveVal_numCtors(v_v_2714_);
    crate::leanh::lean_dec_ref(v_v_2714_);
    return v_res_2715_;
}
pub unsafe fn l_Lean_InductiveVal_isNested(mut v_v_2716_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_numNested_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: u8 = 0;
    v_numNested_2717_ = crate::leanh::lean_ctor_get(v_v_2716_, 5);
    v___x_2718_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2719_ = lean_nat_dec_lt(v___x_2718_, v_numNested_2717_);
    return v___x_2719_;
}
pub unsafe fn l_Lean_InductiveVal_isNested___boxed(
    mut v_v_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2721_: u8 = 0;
    let mut v_r_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Lean_InductiveVal_isNested(v_v_2720_);
    crate::leanh::lean_dec_ref(v_v_2720_);
    v_r_2722_ = crate::leanh::lean_box((v_res_2721_) as usize);
    return v_r_2722_;
}
pub unsafe fn l_Lean_InductiveVal_numTypeFormers(
    mut v_v_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_all_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNested_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_all_2724_ = crate::leanh::lean_ctor_get(v_v_2723_, 3);
    v_numNested_2725_ = crate::leanh::lean_ctor_get(v_v_2723_, 5);
    v___x_2726_ = l_List_lengthTR___redArg(v_all_2724_);
    v___x_2727_ = lean_nat_add(v___x_2726_, v_numNested_2725_);
    crate::leanh::lean_dec(v___x_2726_);
    return v___x_2727_;
}
pub unsafe fn l_Lean_InductiveVal_numTypeFormers___boxed(
    mut v_v_2728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2729_ = l_Lean_InductiveVal_numTypeFormers(v_v_2728_);
    crate::leanh::lean_dec_ref(v_v_2728_);
    return v_res_2729_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstructorVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: u8 = 0;
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = 0;
    v___x_2731_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2732_ = crate::leanh::lean_box(0);
    v___x_2733_ = l_Lean_instInhabitedConstantVal_default;
    v___x_2734_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2734_, 0, v___x_2733_);
    crate::leanh::lean_ctor_set(v___x_2734_, 1, v___x_2732_);
    crate::leanh::lean_ctor_set(v___x_2734_, 2, v___x_2731_);
    crate::leanh::lean_ctor_set(v___x_2734_, 3, v___x_2731_);
    crate::leanh::lean_ctor_set(v___x_2734_, 4, v___x_2731_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2734_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_2730_,
    );
    return v___x_2734_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstructorVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2735_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructorVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructorVal_default___closed__0_once),
        _init_l_Lean_instInhabitedConstructorVal_default___closed__0,
    );
    return v___x_2735_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstructorVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2736_ = l_Lean_instInhabitedConstructorVal_default;
    return v___x_2736_;
}
pub unsafe fn l_Lean_instBEqConstructorVal_beq(
    mut v_x_2737_: *mut crate::leanh::LeanObject,
    mut v_x_2738_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toConstantVal_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_2744_: u8 = 0;
    let mut v_toConstantVal_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isUnsafe_2750_: u8 = 0;
    let mut v___x_2751_: u8 = 0;
    v_toConstantVal_2739_ = crate::leanh::lean_ctor_get(v_x_2737_, 0);
    v_induct_2740_ = crate::leanh::lean_ctor_get(v_x_2737_, 1);
    v_cidx_2741_ = crate::leanh::lean_ctor_get(v_x_2737_, 2);
    v_numParams_2742_ = crate::leanh::lean_ctor_get(v_x_2737_, 3);
    v_numFields_2743_ = crate::leanh::lean_ctor_get(v_x_2737_, 4);
    v_isUnsafe_2744_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2737_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
    );
    v_toConstantVal_2745_ = crate::leanh::lean_ctor_get(v_x_2738_, 0);
    v_induct_2746_ = crate::leanh::lean_ctor_get(v_x_2738_, 1);
    v_cidx_2747_ = crate::leanh::lean_ctor_get(v_x_2738_, 2);
    v_numParams_2748_ = crate::leanh::lean_ctor_get(v_x_2738_, 3);
    v_numFields_2749_ = crate::leanh::lean_ctor_get(v_x_2738_, 4);
    v_isUnsafe_2750_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2738_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
    );
    v___x_2751_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_2739_, v_toConstantVal_2745_);
    if v___x_2751_ == 0 {
        return v___x_2751_;
    } else {
        let mut v___x_2752_: u8 = 0;
        v___x_2752_ = lean_name_eq(v_induct_2740_, v_induct_2746_);
        if v___x_2752_ == 0 {
            return v___x_2752_;
        } else {
            let mut v___x_2753_: u8 = 0;
            v___x_2753_ = lean_nat_dec_eq(v_cidx_2741_, v_cidx_2747_);
            if v___x_2753_ == 0 {
                return v___x_2753_;
            } else {
                let mut v___x_2754_: u8 = 0;
                v___x_2754_ = lean_nat_dec_eq(v_numParams_2742_, v_numParams_2748_);
                if v___x_2754_ == 0 {
                    return v___x_2754_;
                } else {
                    let mut v___x_2755_: u8 = 0;
                    v___x_2755_ = lean_nat_dec_eq(v_numFields_2743_, v_numFields_2749_);
                    if v___x_2755_ == 0 {
                        return v___x_2755_;
                    } else {
                        if v_isUnsafe_2744_ == 0 {
                            if v_isUnsafe_2750_ == 0 {
                                return v___x_2755_;
                            } else {
                                return v_isUnsafe_2744_;
                            }
                        } else {
                            return v_isUnsafe_2750_;
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqConstructorVal_beq___boxed(
    mut v_x_2756_: *mut crate::leanh::LeanObject,
    mut v_x_2757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2758_: u8 = 0;
    let mut v_r_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2758_ = l_Lean_instBEqConstructorVal_beq(v_x_2756_, v_x_2757_);
    crate::leanh::lean_dec_ref(v_x_2757_);
    crate::leanh::lean_dec_ref(v_x_2756_);
    v_r_2759_ = crate::leanh::lean_box((v_res_2758_) as usize);
    return v_r_2759_;
}
pub unsafe fn lean_mk_constructor_val(
    mut v_name_2762_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2763_: *mut crate::leanh::LeanObject,
    mut v_type_2764_: *mut crate::leanh::LeanObject,
    mut v_induct_2765_: *mut crate::leanh::LeanObject,
    mut v_cidx_2766_: *mut crate::leanh::LeanObject,
    mut v_numParams_2767_: *mut crate::leanh::LeanObject,
    mut v_numFields_2768_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2769_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2770_, 0, v_name_2762_);
    crate::leanh::lean_ctor_set(v___x_2770_, 1, v_levelParams_2763_);
    crate::leanh::lean_ctor_set(v___x_2770_, 2, v_type_2764_);
    v___x_2771_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2771_, 0, v___x_2770_);
    crate::leanh::lean_ctor_set(v___x_2771_, 1, v_induct_2765_);
    crate::leanh::lean_ctor_set(v___x_2771_, 2, v_cidx_2766_);
    crate::leanh::lean_ctor_set(v___x_2771_, 3, v_numParams_2767_);
    crate::leanh::lean_ctor_set(v___x_2771_, 4, v_numFields_2768_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2771_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v_isUnsafe_2769_,
    );
    return v___x_2771_;
}
pub unsafe fn l_Lean_mkConstructorValEx___boxed(
    mut v_name_2772_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2773_: *mut crate::leanh::LeanObject,
    mut v_type_2774_: *mut crate::leanh::LeanObject,
    mut v_induct_2775_: *mut crate::leanh::LeanObject,
    mut v_cidx_2776_: *mut crate::leanh::LeanObject,
    mut v_numParams_2777_: *mut crate::leanh::LeanObject,
    mut v_numFields_2778_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isUnsafe_boxed_2780_: u8 = 0;
    let mut v_res_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isUnsafe_boxed_2780_ = (crate::leanh::lean_unbox(v_isUnsafe_2779_) as u8);
    v_res_2781_ = lean_mk_constructor_val(
        v_name_2772_,
        v_levelParams_2773_,
        v_type_2774_,
        v_induct_2775_,
        v_cidx_2776_,
        v_numParams_2777_,
        v_numFields_2778_,
        v_isUnsafe_boxed_2780_,
    );
    return v_res_2781_;
}
pub unsafe fn lean_constructor_val_is_unsafe(mut v_v_2782_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_isUnsafe_2783_: u8 = 0;
    v_isUnsafe_2783_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2782_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2782_);
    return v_isUnsafe_2783_;
}
pub unsafe fn l_Lean_ConstructorVal_isUnsafeEx___boxed(
    mut v_v_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2785_: u8 = 0;
    let mut v_r_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = lean_constructor_val_is_unsafe(v_v_2784_);
    v_r_2786_ = crate::leanh::lean_box((v_res_2785_) as usize);
    return v_r_2786_;
}
pub unsafe fn _init_l_Lean_instInhabitedRecursorRule_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstructor_default___closed__0_once),
        _init_l_Lean_instInhabitedConstructor_default___closed__0,
    );
    v___x_2788_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2789_ = crate::leanh::lean_box(0);
    v___x_2790_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2790_, 0, v___x_2789_);
    crate::leanh::lean_ctor_set(v___x_2790_, 1, v___x_2788_);
    crate::leanh::lean_ctor_set(v___x_2790_, 2, v___x_2787_);
    return v___x_2790_;
}
pub unsafe fn _init_l_Lean_instInhabitedRecursorRule_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedRecursorRule_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedRecursorRule_default___closed__0_once),
        _init_l_Lean_instInhabitedRecursorRule_default___closed__0,
    );
    return v___x_2791_;
}
pub unsafe fn _init_l_Lean_instInhabitedRecursorRule() -> *mut crate::leanh::LeanObject {
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = l_Lean_instInhabitedRecursorRule_default;
    return v___x_2792_;
}
pub unsafe fn l_Lean_instBEqRecursorRule_beq(
    mut v_x_2793_: *mut crate::leanh::LeanObject,
    mut v_x_2794_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_ctor_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nfields_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctor_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nfields_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    v_ctor_2795_ = crate::leanh::lean_ctor_get(v_x_2793_, 0);
    v_nfields_2796_ = crate::leanh::lean_ctor_get(v_x_2793_, 1);
    v_rhs_2797_ = crate::leanh::lean_ctor_get(v_x_2793_, 2);
    v_ctor_2798_ = crate::leanh::lean_ctor_get(v_x_2794_, 0);
    v_nfields_2799_ = crate::leanh::lean_ctor_get(v_x_2794_, 1);
    v_rhs_2800_ = crate::leanh::lean_ctor_get(v_x_2794_, 2);
    v___x_2801_ = lean_name_eq(v_ctor_2795_, v_ctor_2798_);
    if v___x_2801_ == 0 {
        return v___x_2801_;
    } else {
        let mut v___x_2802_: u8 = 0;
        v___x_2802_ = lean_nat_dec_eq(v_nfields_2796_, v_nfields_2799_);
        if v___x_2802_ == 0 {
            return v___x_2802_;
        } else {
            let mut v___x_2803_: u8 = 0;
            v___x_2803_ = lean_expr_eqv(v_rhs_2797_, v_rhs_2800_);
            return v___x_2803_;
        }
    }
}
pub unsafe fn l_Lean_instBEqRecursorRule_beq___boxed(
    mut v_x_2804_: *mut crate::leanh::LeanObject,
    mut v_x_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2806_: u8 = 0;
    let mut v_r_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2806_ = l_Lean_instBEqRecursorRule_beq(v_x_2804_, v_x_2805_);
    crate::leanh::lean_dec_ref(v_x_2805_);
    crate::leanh::lean_dec_ref(v_x_2804_);
    v_r_2807_ = crate::leanh::lean_box((v_res_2806_) as usize);
    return v_r_2807_;
}
pub unsafe fn _init_l_Lean_instInhabitedRecursorVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2810_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2810_ = 0;
    v___x_2811_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2812_ = crate::leanh::lean_box(0);
    v___x_2813_ = l_Lean_instInhabitedConstantVal_default;
    v___x_2814_ = crate::leanh::lean_alloc_ctor(0, 7, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2813_);
    crate::leanh::lean_ctor_set(v___x_2814_, 1, v___x_2812_);
    crate::leanh::lean_ctor_set(v___x_2814_, 2, v___x_2811_);
    crate::leanh::lean_ctor_set(v___x_2814_, 3, v___x_2811_);
    crate::leanh::lean_ctor_set(v___x_2814_, 4, v___x_2811_);
    crate::leanh::lean_ctor_set(v___x_2814_, 5, v___x_2811_);
    crate::leanh::lean_ctor_set(v___x_2814_, 6, v___x_2812_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2814_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_2810_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2814_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v___x_2810_,
    );
    return v___x_2814_;
}
pub unsafe fn _init_l_Lean_instInhabitedRecursorVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2815_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedRecursorVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedRecursorVal_default___closed__0_once),
        _init_l_Lean_instInhabitedRecursorVal_default___closed__0,
    );
    return v___x_2815_;
}
pub unsafe fn _init_l_Lean_instInhabitedRecursorVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2816_ = l_Lean_instInhabitedRecursorVal_default;
    return v___x_2816_;
}
pub unsafe fn l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(
    mut v_x_2817_: *mut crate::leanh::LeanObject,
    mut v_x_2818_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: u8 = 0;
    let mut v_head_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2817_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_2818_) == 0 {
                        v___x_2819_ = 1;
                        return v___x_2819_;
                    } else {
                        v___x_2820_ = 0;
                        return v___x_2820_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_2818_) == 0 {
                        v___x_2821_ = 0;
                        return v___x_2821_;
                    } else {
                        v_head_2822_ = crate::leanh::lean_ctor_get(v_x_2817_, 0);
                        v_tail_2823_ = crate::leanh::lean_ctor_get(v_x_2817_, 1);
                        v_head_2824_ = crate::leanh::lean_ctor_get(v_x_2818_, 0);
                        v_tail_2825_ = crate::leanh::lean_ctor_get(v_x_2818_, 1);
                        v___x_2826_ = l_Lean_instBEqRecursorRule_beq(v_head_2822_, v_head_2824_);
                        if v___x_2826_ == 0 {
                            return v___x_2826_;
                        } else {
                            v_x_2817_ = v_tail_2823_;
                            v_x_2818_ = v_tail_2825_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(
    mut v_x_2828_: *mut crate::leanh::LeanObject,
    mut v_x_2829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2830_: u8 = 0;
    let mut v_r_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2830_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_2828_, v_x_2829_);
    crate::leanh::lean_dec(v_x_2829_);
    crate::leanh::lean_dec(v_x_2828_);
    v_r_2831_ = crate::leanh::lean_box((v_res_2830_) as usize);
    return v_r_2831_;
}
pub unsafe fn l_Lean_instBEqRecursorVal_beq(
    mut v_x_2832_: *mut crate::leanh::LeanObject,
    mut v_x_2833_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toConstantVal_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMinors_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2841_: u8 = 0;
    let mut v_isUnsafe_2842_: u8 = 0;
    let mut v_toConstantVal_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMinors_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2850_: u8 = 0;
    let mut v_isUnsafe_2851_: u8 = 0;
    let mut v___y_2853_: u8 = 0;
    let mut v___x_2854_: u8 = 0;
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toConstantVal_2834_ = crate::leanh::lean_ctor_get(v_x_2832_, 0);
                v_all_2835_ = crate::leanh::lean_ctor_get(v_x_2832_, 1);
                v_numParams_2836_ = crate::leanh::lean_ctor_get(v_x_2832_, 2);
                v_numIndices_2837_ = crate::leanh::lean_ctor_get(v_x_2832_, 3);
                v_numMotives_2838_ = crate::leanh::lean_ctor_get(v_x_2832_, 4);
                v_numMinors_2839_ = crate::leanh::lean_ctor_get(v_x_2832_, 5);
                v_rules_2840_ = crate::leanh::lean_ctor_get(v_x_2832_, 6);
                v_k_2841_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2832_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_isUnsafe_2842_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2832_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_toConstantVal_2843_ = crate::leanh::lean_ctor_get(v_x_2833_, 0);
                v_all_2844_ = crate::leanh::lean_ctor_get(v_x_2833_, 1);
                v_numParams_2845_ = crate::leanh::lean_ctor_get(v_x_2833_, 2);
                v_numIndices_2846_ = crate::leanh::lean_ctor_get(v_x_2833_, 3);
                v_numMotives_2847_ = crate::leanh::lean_ctor_get(v_x_2833_, 4);
                v_numMinors_2848_ = crate::leanh::lean_ctor_get(v_x_2833_, 5);
                v_rules_2849_ = crate::leanh::lean_ctor_get(v_x_2833_, 6);
                v_k_2850_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2833_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_isUnsafe_2851_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_2833_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v___x_2854_ =
                    l_Lean_instBEqConstantVal_beq(v_toConstantVal_2834_, v_toConstantVal_2843_);
                if v___x_2854_ == 0 {
                    return v___x_2854_;
                } else {
                    v___x_2855_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(
                        v_all_2835_,
                        v_all_2844_,
                    );
                    if v___x_2855_ == 0 {
                        return v___x_2855_;
                    } else {
                        v___x_2856_ = lean_nat_dec_eq(v_numParams_2836_, v_numParams_2845_);
                        if v___x_2856_ == 0 {
                            return v___x_2856_;
                        } else {
                            v___x_2857_ = lean_nat_dec_eq(v_numIndices_2837_, v_numIndices_2846_);
                            if v___x_2857_ == 0 {
                                return v___x_2857_;
                            } else {
                                v___x_2858_ =
                                    lean_nat_dec_eq(v_numMotives_2838_, v_numMotives_2847_);
                                if v___x_2858_ == 0 {
                                    return v___x_2858_;
                                } else {
                                    v___x_2859_ =
                                        lean_nat_dec_eq(v_numMinors_2839_, v_numMinors_2848_);
                                    if v___x_2859_ == 0 {
                                        return v___x_2859_;
                                    } else {
                                        v___x_2860_ =
                                            l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(
                                                v_rules_2840_,
                                                v_rules_2849_,
                                            );
                                        if v___x_2860_ == 0 {
                                            return v___x_2860_;
                                        } else {
                                            if v_k_2841_ == 0 {
                                                if v_k_2850_ == 0 {
                                                    v___y_2853_ = v___x_2860_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    return v_k_2841_;
                                                }
                                            } else {
                                                v___y_2853_ = v_k_2850_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_2853_ == 0 {
                    return v___y_2853_;
                } else {
                    if v_isUnsafe_2842_ == 0 {
                        if v_isUnsafe_2851_ == 0 {
                            return v___y_2853_;
                        } else {
                            return v_isUnsafe_2842_;
                        }
                    } else {
                        return v_isUnsafe_2851_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instBEqRecursorVal_beq___boxed(
    mut v_x_2861_: *mut crate::leanh::LeanObject,
    mut v_x_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2863_: u8 = 0;
    let mut v_r_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2863_ = l_Lean_instBEqRecursorVal_beq(v_x_2861_, v_x_2862_);
    crate::leanh::lean_dec_ref(v_x_2862_);
    crate::leanh::lean_dec_ref(v_x_2861_);
    v_r_2864_ = crate::leanh::lean_box((v_res_2863_) as usize);
    return v_r_2864_;
}
pub unsafe fn lean_mk_recursor_val(
    mut v_name_2867_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2868_: *mut crate::leanh::LeanObject,
    mut v_type_2869_: *mut crate::leanh::LeanObject,
    mut v_all_2870_: *mut crate::leanh::LeanObject,
    mut v_numParams_2871_: *mut crate::leanh::LeanObject,
    mut v_numIndices_2872_: *mut crate::leanh::LeanObject,
    mut v_numMotives_2873_: *mut crate::leanh::LeanObject,
    mut v_numMinors_2874_: *mut crate::leanh::LeanObject,
    mut v_rules_2875_: *mut crate::leanh::LeanObject,
    mut v_k_2876_: u8,
    mut v_isUnsafe_2877_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2878_, 0, v_name_2867_);
    crate::leanh::lean_ctor_set(v___x_2878_, 1, v_levelParams_2868_);
    crate::leanh::lean_ctor_set(v___x_2878_, 2, v_type_2869_);
    v___x_2879_ = crate::leanh::lean_alloc_ctor(0, 7, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2878_);
    crate::leanh::lean_ctor_set(v___x_2879_, 1, v_all_2870_);
    crate::leanh::lean_ctor_set(v___x_2879_, 2, v_numParams_2871_);
    crate::leanh::lean_ctor_set(v___x_2879_, 3, v_numIndices_2872_);
    crate::leanh::lean_ctor_set(v___x_2879_, 4, v_numMotives_2873_);
    crate::leanh::lean_ctor_set(v___x_2879_, 5, v_numMinors_2874_);
    crate::leanh::lean_ctor_set(v___x_2879_, 6, v_rules_2875_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2879_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v_k_2876_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2879_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v_isUnsafe_2877_,
    );
    return v___x_2879_;
}
pub unsafe fn l_Lean_mkRecursorValEx___boxed(
    mut v_name_2880_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2881_: *mut crate::leanh::LeanObject,
    mut v_type_2882_: *mut crate::leanh::LeanObject,
    mut v_all_2883_: *mut crate::leanh::LeanObject,
    mut v_numParams_2884_: *mut crate::leanh::LeanObject,
    mut v_numIndices_2885_: *mut crate::leanh::LeanObject,
    mut v_numMotives_2886_: *mut crate::leanh::LeanObject,
    mut v_numMinors_2887_: *mut crate::leanh::LeanObject,
    mut v_rules_2888_: *mut crate::leanh::LeanObject,
    mut v_k_2889_: *mut crate::leanh::LeanObject,
    mut v_isUnsafe_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_boxed_2891_: u8 = 0;
    let mut v_isUnsafe_boxed_2892_: u8 = 0;
    let mut v_res_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_boxed_2891_ = (crate::leanh::lean_unbox(v_k_2889_) as u8);
    v_isUnsafe_boxed_2892_ = (crate::leanh::lean_unbox(v_isUnsafe_2890_) as u8);
    v_res_2893_ = lean_mk_recursor_val(
        v_name_2880_,
        v_levelParams_2881_,
        v_type_2882_,
        v_all_2883_,
        v_numParams_2884_,
        v_numIndices_2885_,
        v_numMotives_2886_,
        v_numMinors_2887_,
        v_rules_2888_,
        v_k_boxed_2891_,
        v_isUnsafe_boxed_2892_,
    );
    return v_res_2893_;
}
pub unsafe fn lean_recursor_k(mut v_v_2894_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_k_2895_: u8 = 0;
    v_k_2895_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2894_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2894_);
    return v_k_2895_;
}
pub unsafe fn l_Lean_RecursorVal_kEx___boxed(
    mut v_v_2896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2897_: u8 = 0;
    let mut v_r_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2897_ = lean_recursor_k(v_v_2896_);
    v_r_2898_ = crate::leanh::lean_box((v_res_2897_) as usize);
    return v_r_2898_;
}
pub unsafe fn lean_recursor_is_unsafe(mut v_v_2899_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_isUnsafe_2900_: u8 = 0;
    v_isUnsafe_2900_ = crate::leanh::lean_ctor_get_uint8(
        v_v_2899_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_2899_);
    return v_isUnsafe_2900_;
}
pub unsafe fn l_Lean_RecursorVal_isUnsafeEx___boxed(
    mut v_v_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2902_: u8 = 0;
    let mut v_r_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = lean_recursor_is_unsafe(v_v_2901_);
    v_r_2903_ = crate::leanh::lean_box((v_res_2902_) as usize);
    return v_r_2903_;
}
pub unsafe fn l_Lean_RecursorVal_getMajorIdx(
    mut v_v_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMinors_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_numParams_2905_ = crate::leanh::lean_ctor_get(v_v_2904_, 2);
    v_numIndices_2906_ = crate::leanh::lean_ctor_get(v_v_2904_, 3);
    v_numMotives_2907_ = crate::leanh::lean_ctor_get(v_v_2904_, 4);
    v_numMinors_2908_ = crate::leanh::lean_ctor_get(v_v_2904_, 5);
    v___x_2909_ = lean_nat_add(v_numParams_2905_, v_numMotives_2907_);
    v___x_2910_ = lean_nat_add(v___x_2909_, v_numMinors_2908_);
    crate::leanh::lean_dec(v___x_2909_);
    v___x_2911_ = lean_nat_add(v___x_2910_, v_numIndices_2906_);
    crate::leanh::lean_dec(v___x_2910_);
    return v___x_2911_;
}
pub unsafe fn l_Lean_RecursorVal_getMajorIdx___boxed(
    mut v_v_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Lean_RecursorVal_getMajorIdx(v_v_2912_);
    crate::leanh::lean_dec_ref(v_v_2912_);
    return v_res_2913_;
}
pub unsafe fn l_Lean_RecursorVal_getFirstIndexIdx(
    mut v_v_2914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMinors_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_numParams_2915_ = crate::leanh::lean_ctor_get(v_v_2914_, 2);
    v_numMotives_2916_ = crate::leanh::lean_ctor_get(v_v_2914_, 4);
    v_numMinors_2917_ = crate::leanh::lean_ctor_get(v_v_2914_, 5);
    v___x_2918_ = lean_nat_add(v_numParams_2915_, v_numMotives_2916_);
    v___x_2919_ = lean_nat_add(v___x_2918_, v_numMinors_2917_);
    crate::leanh::lean_dec(v___x_2918_);
    return v___x_2919_;
}
pub unsafe fn l_Lean_RecursorVal_getFirstIndexIdx___boxed(
    mut v_v_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_2920_);
    crate::leanh::lean_dec_ref(v_v_2920_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_RecursorVal_getFirstMinorIdx(
    mut v_v_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_numParams_2923_ = crate::leanh::lean_ctor_get(v_v_2922_, 2);
    v_numMotives_2924_ = crate::leanh::lean_ctor_get(v_v_2922_, 4);
    v___x_2925_ = lean_nat_add(v_numParams_2923_, v_numMotives_2924_);
    return v___x_2925_;
}
pub unsafe fn l_Lean_RecursorVal_getFirstMinorIdx___boxed(
    mut v_v_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2927_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_2926_);
    crate::leanh::lean_dec_ref(v_v_2926_);
    return v_res_2927_;
}
pub unsafe fn l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(
    mut v_x_2928_: *mut crate::leanh::LeanObject,
    mut v_x_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2931_: u8 = 0;
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2930_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2931_ = lean_nat_dec_eq(v_x_2928_, v_zero_2930_);
                if v_isZero_2931_ == 1 {
                    crate::leanh::lean_dec(v_x_2928_);
                    v___x_2932_ = l_Lean_Expr_bindingDomain_x21(v_x_2929_);
                    crate::leanh::lean_dec_ref(v_x_2929_);
                    v___x_2933_ = l_Lean_Expr_getAppFn(v___x_2932_);
                    crate::leanh::lean_dec_ref(v___x_2932_);
                    v___x_2934_ = l_Lean_Expr_constName_x21(v___x_2933_);
                    crate::leanh::lean_dec_ref(v___x_2933_);
                    return v___x_2934_;
                } else {
                    v_one_2935_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2936_ = lean_nat_sub(v_x_2928_, v_one_2935_);
                    crate::leanh::lean_dec(v_x_2928_);
                    v___x_2937_ = l_Lean_Expr_bindingBody_x21(v_x_2929_);
                    crate::leanh::lean_dec_ref(v_x_2929_);
                    v_x_2928_ = v_n_2936_;
                    v_x_2929_ = v___x_2937_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RecursorVal_getMajorInduct(
    mut v_v_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toConstantVal_2940_ = crate::leanh::lean_ctor_get(v_v_2939_, 0);
    v_type_2941_ = crate::leanh::lean_ctor_get(v_toConstantVal_2940_, 2);
    crate::leanh::lean_inc_ref(v_type_2941_);
    v___x_2942_ = l_Lean_RecursorVal_getMajorIdx(v_v_2939_);
    crate::leanh::lean_dec_ref(v_v_2939_);
    v___x_2943_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(
        v___x_2942_,
        v_type_2941_,
    );
    return v___x_2943_;
}
pub unsafe fn l_Lean_QuotKind_ctorIdx(mut v_x_2944_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_2944_ {
        0 => {
            let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2945_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2945_;
        }
        1 => {
            let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2946_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2946_;
        }
        2 => {
            let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2947_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2947_;
        }
        _ => {
            let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2948_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2948_;
        }
    }
}
pub unsafe fn l_Lean_QuotKind_ctorIdx___boxed(
    mut v_x_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2950_: u8 = 0;
    let mut v_res_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2950_ = (crate::leanh::lean_unbox(v_x_2949_) as u8);
    v_res_2951_ = l_Lean_QuotKind_ctorIdx(v_x_boxed_2950_);
    return v_res_2951_;
}
pub unsafe fn l_Lean_QuotKind_toCtorIdx(mut v_x_2952_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = l_Lean_QuotKind_ctorIdx(v_x_2952_);
    return v___x_2953_;
}
pub unsafe fn l_Lean_QuotKind_toCtorIdx___boxed(
    mut v_x_2954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2955_: u8 = 0;
    let mut v_res_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2955_ = (crate::leanh::lean_unbox(v_x_2954_) as u8);
    v_res_2956_ = l_Lean_QuotKind_toCtorIdx(v_x_4__boxed_2955_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_QuotKind_ctorElim___redArg(
    mut v_k_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2957_);
    return v_k_2957_;
}
pub unsafe fn l_Lean_QuotKind_ctorElim___redArg___boxed(
    mut v_k_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2959_ = l_Lean_QuotKind_ctorElim___redArg(v_k_2958_);
    crate::leanh::lean_dec(v_k_2958_);
    return v_res_2959_;
}
pub unsafe fn l_Lean_QuotKind_ctorElim(
    mut v_motive_2960_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2961_: *mut crate::leanh::LeanObject,
    mut v_t_2962_: u8,
    mut v_h_2963_: *mut crate::leanh::LeanObject,
    mut v_k_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2964_);
    return v_k_2964_;
}
pub unsafe fn l_Lean_QuotKind_ctorElim___boxed(
    mut v_motive_2965_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2966_: *mut crate::leanh::LeanObject,
    mut v_t_2967_: *mut crate::leanh::LeanObject,
    mut v_h_2968_: *mut crate::leanh::LeanObject,
    mut v_k_2969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2970_: u8 = 0;
    let mut v_res_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2970_ = (crate::leanh::lean_unbox(v_t_2967_) as u8);
    v_res_2971_ = l_Lean_QuotKind_ctorElim(
        v_motive_2965_,
        v_ctorIdx_2966_,
        v_t_boxed_2970_,
        v_h_2968_,
        v_k_2969_,
    );
    crate::leanh::lean_dec(v_k_2969_);
    crate::leanh::lean_dec(v_ctorIdx_2966_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_QuotKind_type_elim___redArg(
    mut v_type_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_type_2972_);
    return v_type_2972_;
}
pub unsafe fn l_Lean_QuotKind_type_elim___redArg___boxed(
    mut v_type_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2974_ = l_Lean_QuotKind_type_elim___redArg(v_type_2973_);
    crate::leanh::lean_dec(v_type_2973_);
    return v_res_2974_;
}
pub unsafe fn l_Lean_QuotKind_type_elim(
    mut v_motive_2975_: *mut crate::leanh::LeanObject,
    mut v_t_2976_: u8,
    mut v_h_2977_: *mut crate::leanh::LeanObject,
    mut v_type_2978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_type_2978_);
    return v_type_2978_;
}
pub unsafe fn l_Lean_QuotKind_type_elim___boxed(
    mut v_motive_2979_: *mut crate::leanh::LeanObject,
    mut v_t_2980_: *mut crate::leanh::LeanObject,
    mut v_h_2981_: *mut crate::leanh::LeanObject,
    mut v_type_2982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2983_: u8 = 0;
    let mut v_res_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2983_ = (crate::leanh::lean_unbox(v_t_2980_) as u8);
    v_res_2984_ =
        l_Lean_QuotKind_type_elim(v_motive_2979_, v_t_boxed_2983_, v_h_2981_, v_type_2982_);
    crate::leanh::lean_dec(v_type_2982_);
    return v_res_2984_;
}
pub unsafe fn l_Lean_QuotKind_ctor_elim___redArg(
    mut v_ctor_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ctor_2985_);
    return v_ctor_2985_;
}
pub unsafe fn l_Lean_QuotKind_ctor_elim___redArg___boxed(
    mut v_ctor_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2987_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_2986_);
    crate::leanh::lean_dec(v_ctor_2986_);
    return v_res_2987_;
}
pub unsafe fn l_Lean_QuotKind_ctor_elim(
    mut v_motive_2988_: *mut crate::leanh::LeanObject,
    mut v_t_2989_: u8,
    mut v_h_2990_: *mut crate::leanh::LeanObject,
    mut v_ctor_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ctor_2991_);
    return v_ctor_2991_;
}
pub unsafe fn l_Lean_QuotKind_ctor_elim___boxed(
    mut v_motive_2992_: *mut crate::leanh::LeanObject,
    mut v_t_2993_: *mut crate::leanh::LeanObject,
    mut v_h_2994_: *mut crate::leanh::LeanObject,
    mut v_ctor_2995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2996_: u8 = 0;
    let mut v_res_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2996_ = (crate::leanh::lean_unbox(v_t_2993_) as u8);
    v_res_2997_ =
        l_Lean_QuotKind_ctor_elim(v_motive_2992_, v_t_boxed_2996_, v_h_2994_, v_ctor_2995_);
    crate::leanh::lean_dec(v_ctor_2995_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_QuotKind_lift_elim___redArg(
    mut v_lift_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lift_2998_);
    return v_lift_2998_;
}
pub unsafe fn l_Lean_QuotKind_lift_elim___redArg___boxed(
    mut v_lift_2999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3000_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_2999_);
    crate::leanh::lean_dec(v_lift_2999_);
    return v_res_3000_;
}
pub unsafe fn l_Lean_QuotKind_lift_elim(
    mut v_motive_3001_: *mut crate::leanh::LeanObject,
    mut v_t_3002_: u8,
    mut v_h_3003_: *mut crate::leanh::LeanObject,
    mut v_lift_3004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lift_3004_);
    return v_lift_3004_;
}
pub unsafe fn l_Lean_QuotKind_lift_elim___boxed(
    mut v_motive_3005_: *mut crate::leanh::LeanObject,
    mut v_t_3006_: *mut crate::leanh::LeanObject,
    mut v_h_3007_: *mut crate::leanh::LeanObject,
    mut v_lift_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3009_: u8 = 0;
    let mut v_res_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3009_ = (crate::leanh::lean_unbox(v_t_3006_) as u8);
    v_res_3010_ =
        l_Lean_QuotKind_lift_elim(v_motive_3005_, v_t_boxed_3009_, v_h_3007_, v_lift_3008_);
    crate::leanh::lean_dec(v_lift_3008_);
    return v_res_3010_;
}
pub unsafe fn l_Lean_QuotKind_ind_elim___redArg(
    mut v_ind_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ind_3011_);
    return v_ind_3011_;
}
pub unsafe fn l_Lean_QuotKind_ind_elim___redArg___boxed(
    mut v_ind_3012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3013_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_3012_);
    crate::leanh::lean_dec(v_ind_3012_);
    return v_res_3013_;
}
pub unsafe fn l_Lean_QuotKind_ind_elim(
    mut v_motive_3014_: *mut crate::leanh::LeanObject,
    mut v_t_3015_: u8,
    mut v_h_3016_: *mut crate::leanh::LeanObject,
    mut v_ind_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ind_3017_);
    return v_ind_3017_;
}
pub unsafe fn l_Lean_QuotKind_ind_elim___boxed(
    mut v_motive_3018_: *mut crate::leanh::LeanObject,
    mut v_t_3019_: *mut crate::leanh::LeanObject,
    mut v_h_3020_: *mut crate::leanh::LeanObject,
    mut v_ind_3021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3022_: u8 = 0;
    let mut v_res_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3022_ = (crate::leanh::lean_unbox(v_t_3019_) as u8);
    v_res_3023_ = l_Lean_QuotKind_ind_elim(v_motive_3018_, v_t_boxed_3022_, v_h_3020_, v_ind_3021_);
    crate::leanh::lean_dec(v_ind_3021_);
    return v_res_3023_;
}
pub unsafe fn _init_l_Lean_instInhabitedQuotKind_default() -> u8 {
    let mut v___x_3024_: u8 = 0;
    v___x_3024_ = 0;
    return v___x_3024_;
}
pub unsafe fn _init_l_Lean_instInhabitedQuotKind() -> u8 {
    let mut v___x_3025_: u8 = 0;
    v___x_3025_ = 0;
    return v___x_3025_;
}
pub unsafe fn _init_l_Lean_instInhabitedQuotVal_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3026_: u8 = 0;
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3026_ = 0;
    v___x_3027_ = l_Lean_instInhabitedConstantVal_default;
    v___x_3028_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3028_, 0, v___x_3027_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3028_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3026_,
    );
    return v___x_3028_;
}
pub unsafe fn _init_l_Lean_instInhabitedQuotVal_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3029_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedQuotVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedQuotVal_default___closed__0_once),
        _init_l_Lean_instInhabitedQuotVal_default___closed__0,
    );
    return v___x_3029_;
}
pub unsafe fn _init_l_Lean_instInhabitedQuotVal() -> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = l_Lean_instInhabitedQuotVal_default;
    return v___x_3030_;
}
pub unsafe fn lean_mk_quot_val(
    mut v_name_3031_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3032_: *mut crate::leanh::LeanObject,
    mut v_type_3033_: *mut crate::leanh::LeanObject,
    mut v_kind_3034_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3035_, 0, v_name_3031_);
    crate::leanh::lean_ctor_set(v___x_3035_, 1, v_levelParams_3032_);
    crate::leanh::lean_ctor_set(v___x_3035_, 2, v_type_3033_);
    v___x_3036_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3036_, 0, v___x_3035_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3036_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_kind_3034_,
    );
    return v___x_3036_;
}
pub unsafe fn l_Lean_mkQuotValEx___boxed(
    mut v_name_3037_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3038_: *mut crate::leanh::LeanObject,
    mut v_type_3039_: *mut crate::leanh::LeanObject,
    mut v_kind_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_3041_: u8 = 0;
    let mut v_res_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3041_ = (crate::leanh::lean_unbox(v_kind_3040_) as u8);
    v_res_3042_ = lean_mk_quot_val(
        v_name_3037_,
        v_levelParams_3038_,
        v_type_3039_,
        v_kind_boxed_3041_,
    );
    return v_res_3042_;
}
pub unsafe fn lean_quot_val_kind(mut v_v_3043_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_kind_3044_: u8 = 0;
    v_kind_3044_ = crate::leanh::lean_ctor_get_uint8(
        v_v_3043_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    crate::leanh::lean_dec_ref(v_v_3043_);
    return v_kind_3044_;
}
pub unsafe fn l_Lean_QuotVal_kindEx___boxed(
    mut v_v_3045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3046_: u8 = 0;
    let mut v_r_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3046_ = lean_quot_val_kind(v_v_3045_);
    v_r_3047_ = crate::leanh::lean_box((v_res_3046_) as usize);
    return v_r_3047_;
}
pub unsafe fn l_Lean_ConstantInfo_ctorIdx(
    mut v_x_3048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3048_) {
        0 => {
            let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3049_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3049_;
        }
        1 => {
            let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3050_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3050_;
        }
        2 => {
            let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3051_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3051_;
        }
        3 => {
            let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3052_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_3052_;
        }
        4 => {
            let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3053_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_3053_;
        }
        5 => {
            let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3054_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_3054_;
        }
        6 => {
            let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3055_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_3055_;
        }
        _ => {
            let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3056_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_3056_;
        }
    }
}
pub unsafe fn l_Lean_ConstantInfo_ctorIdx___boxed(
    mut v_x_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ = l_Lean_ConstantInfo_ctorIdx(v_x_3057_);
    crate::leanh::lean_dec_ref(v_x_3057_);
    return v_res_3058_;
}
pub unsafe fn l_Lean_ConstantInfo_ctorElim___redArg(
    mut v_t_3059_: *mut crate::leanh::LeanObject,
    mut v_k_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_3061_ = crate::leanh::lean_ctor_get(v_t_3059_, 0);
    crate::leanh::lean_inc_ref(v_val_3061_);
    crate::leanh::lean_dec_ref(v_t_3059_);
    v___x_3062_ = crate::leanh::lean_apply_1(v_k_3060_, v_val_3061_);
    return v___x_3062_;
}
pub unsafe fn l_Lean_ConstantInfo_ctorElim(
    mut v_motive_3063_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3064_: *mut crate::leanh::LeanObject,
    mut v_t_3065_: *mut crate::leanh::LeanObject,
    mut v_h_3066_: *mut crate::leanh::LeanObject,
    mut v_k_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3065_, v_k_3067_);
    return v___x_3068_;
}
pub unsafe fn l_Lean_ConstantInfo_ctorElim___boxed(
    mut v_motive_3069_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3070_: *mut crate::leanh::LeanObject,
    mut v_t_3071_: *mut crate::leanh::LeanObject,
    mut v_h_3072_: *mut crate::leanh::LeanObject,
    mut v_k_3073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_ConstantInfo_ctorElim(
        v_motive_3069_,
        v_ctorIdx_3070_,
        v_t_3071_,
        v_h_3072_,
        v_k_3073_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3070_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_ConstantInfo_axiomInfo_elim___redArg(
    mut v_t_3075_: *mut crate::leanh::LeanObject,
    mut v_axiomInfo_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3077_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3075_, v_axiomInfo_3076_);
    return v___x_3077_;
}
pub unsafe fn l_Lean_ConstantInfo_axiomInfo_elim(
    mut v_motive_3078_: *mut crate::leanh::LeanObject,
    mut v_t_3079_: *mut crate::leanh::LeanObject,
    mut v_h_3080_: *mut crate::leanh::LeanObject,
    mut v_axiomInfo_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3082_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3079_, v_axiomInfo_3081_);
    return v___x_3082_;
}
pub unsafe fn l_Lean_ConstantInfo_defnInfo_elim___redArg(
    mut v_t_3083_: *mut crate::leanh::LeanObject,
    mut v_defnInfo_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3085_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3083_, v_defnInfo_3084_);
    return v___x_3085_;
}
pub unsafe fn l_Lean_ConstantInfo_defnInfo_elim(
    mut v_motive_3086_: *mut crate::leanh::LeanObject,
    mut v_t_3087_: *mut crate::leanh::LeanObject,
    mut v_h_3088_: *mut crate::leanh::LeanObject,
    mut v_defnInfo_3089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3087_, v_defnInfo_3089_);
    return v___x_3090_;
}
pub unsafe fn l_Lean_ConstantInfo_thmInfo_elim___redArg(
    mut v_t_3091_: *mut crate::leanh::LeanObject,
    mut v_thmInfo_3092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3091_, v_thmInfo_3092_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_ConstantInfo_thmInfo_elim(
    mut v_motive_3094_: *mut crate::leanh::LeanObject,
    mut v_t_3095_: *mut crate::leanh::LeanObject,
    mut v_h_3096_: *mut crate::leanh::LeanObject,
    mut v_thmInfo_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3098_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3095_, v_thmInfo_3097_);
    return v___x_3098_;
}
pub unsafe fn l_Lean_ConstantInfo_opaqueInfo_elim___redArg(
    mut v_t_3099_: *mut crate::leanh::LeanObject,
    mut v_opaqueInfo_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3099_, v_opaqueInfo_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_ConstantInfo_opaqueInfo_elim(
    mut v_motive_3102_: *mut crate::leanh::LeanObject,
    mut v_t_3103_: *mut crate::leanh::LeanObject,
    mut v_h_3104_: *mut crate::leanh::LeanObject,
    mut v_opaqueInfo_3105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3103_, v_opaqueInfo_3105_);
    return v___x_3106_;
}
pub unsafe fn l_Lean_ConstantInfo_quotInfo_elim___redArg(
    mut v_t_3107_: *mut crate::leanh::LeanObject,
    mut v_quotInfo_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3109_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3107_, v_quotInfo_3108_);
    return v___x_3109_;
}
pub unsafe fn l_Lean_ConstantInfo_quotInfo_elim(
    mut v_motive_3110_: *mut crate::leanh::LeanObject,
    mut v_t_3111_: *mut crate::leanh::LeanObject,
    mut v_h_3112_: *mut crate::leanh::LeanObject,
    mut v_quotInfo_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3111_, v_quotInfo_3113_);
    return v___x_3114_;
}
pub unsafe fn l_Lean_ConstantInfo_inductInfo_elim___redArg(
    mut v_t_3115_: *mut crate::leanh::LeanObject,
    mut v_inductInfo_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3117_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3115_, v_inductInfo_3116_);
    return v___x_3117_;
}
pub unsafe fn l_Lean_ConstantInfo_inductInfo_elim(
    mut v_motive_3118_: *mut crate::leanh::LeanObject,
    mut v_t_3119_: *mut crate::leanh::LeanObject,
    mut v_h_3120_: *mut crate::leanh::LeanObject,
    mut v_inductInfo_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3122_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3119_, v_inductInfo_3121_);
    return v___x_3122_;
}
pub unsafe fn l_Lean_ConstantInfo_ctorInfo_elim___redArg(
    mut v_t_3123_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3125_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3123_, v_ctorInfo_3124_);
    return v___x_3125_;
}
pub unsafe fn l_Lean_ConstantInfo_ctorInfo_elim(
    mut v_motive_3126_: *mut crate::leanh::LeanObject,
    mut v_t_3127_: *mut crate::leanh::LeanObject,
    mut v_h_3128_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3130_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3127_, v_ctorInfo_3129_);
    return v___x_3130_;
}
pub unsafe fn l_Lean_ConstantInfo_recInfo_elim___redArg(
    mut v_t_3131_: *mut crate::leanh::LeanObject,
    mut v_recInfo_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3133_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3131_, v_recInfo_3132_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_ConstantInfo_recInfo_elim(
    mut v_motive_3134_: *mut crate::leanh::LeanObject,
    mut v_t_3135_: *mut crate::leanh::LeanObject,
    mut v_h_3136_: *mut crate::leanh::LeanObject,
    mut v_recInfo_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_3135_, v_recInfo_3137_);
    return v___x_3138_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstantInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3139_ = l_Lean_instInhabitedAxiomVal_default;
    v___x_3140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3139_);
    return v___x_3140_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstantInfo_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3141_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstantInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedConstantInfo_default___closed__0_once),
        _init_l_Lean_instInhabitedConstantInfo_default___closed__0,
    );
    return v___x_3141_;
}
pub unsafe fn _init_l_Lean_instInhabitedConstantInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Lean_instInhabitedConstantInfo_default;
    return v___x_3142_;
}
pub unsafe fn l_Lean_ConstantInfo_toConstantVal(
    mut v_x_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_3144_ = crate::leanh::lean_ctor_get(v_x_3143_, 0);
    v_toConstantVal_3145_ = crate::leanh::lean_ctor_get(v_val_3144_, 0);
    crate::leanh::lean_inc_ref(v_toConstantVal_3145_);
    return v_toConstantVal_3145_;
}
pub unsafe fn l_Lean_ConstantInfo_toConstantVal___boxed(
    mut v_x_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Lean_ConstantInfo_toConstantVal(v_x_3146_);
    crate::leanh::lean_dec_ref(v_x_3146_);
    return v_res_3147_;
}
pub unsafe fn l_Lean_ConstantInfo_isUnsafe(mut v_x_3148_: *mut crate::leanh::LeanObject) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_3148_) {
        0 => {
            let mut v_val_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isUnsafe_3150_: u8 = 0;
            v_val_3149_ = crate::leanh::lean_ctor_get(v_x_3148_, 0);
            v_isUnsafe_3150_ = crate::leanh::lean_ctor_get_uint8(
                v_val_3149_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            );
            return v_isUnsafe_3150_;
        }
        1 => {
            let mut v_val_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_safety_3152_: u8 = 0;
            let mut v___x_3153_: u8 = 0;
            let mut v___x_3154_: u8 = 0;
            v_val_3151_ = crate::leanh::lean_ctor_get(v_x_3148_, 0);
            v_safety_3152_ = crate::leanh::lean_ctor_get_uint8(
                v_val_3151_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            v___x_3153_ = 0;
            v___x_3154_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3152_, v___x_3153_);
            return v___x_3154_;
        }
        3 => {
            let mut v_val_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isUnsafe_3156_: u8 = 0;
            v_val_3155_ = crate::leanh::lean_ctor_get(v_x_3148_, 0);
            v_isUnsafe_3156_ = crate::leanh::lean_ctor_get_uint8(
                v_val_3155_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            return v_isUnsafe_3156_;
        }
        5 => {
            let mut v_val_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isUnsafe_3158_: u8 = 0;
            v_val_3157_ = crate::leanh::lean_ctor_get(v_x_3148_, 0);
            v_isUnsafe_3158_ = crate::leanh::lean_ctor_get_uint8(
                v_val_3157_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 1) as u32,
            );
            return v_isUnsafe_3158_;
        }
        6 => {
            let mut v_val_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isUnsafe_3160_: u8 = 0;
            v_val_3159_ = crate::leanh::lean_ctor_get(v_x_3148_, 0);
            v_isUnsafe_3160_ = crate::leanh::lean_ctor_get_uint8(
                v_val_3159_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
            );
            return v_isUnsafe_3160_;
        }
        7 => {
            let mut v_val_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isUnsafe_3162_: u8 = 0;
            v_val_3161_ = crate::leanh::lean_ctor_get(v_x_3148_, 0);
            v_isUnsafe_3162_ = crate::leanh::lean_ctor_get_uint8(
                v_val_3161_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
            );
            return v_isUnsafe_3162_;
        }
        _ => {
            let mut v___x_3163_: u8 = 0;
            v___x_3163_ = 0;
            return v___x_3163_;
        }
    }
}
pub unsafe fn l_Lean_ConstantInfo_isUnsafe___boxed(
    mut v_x_3164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3165_: u8 = 0;
    let mut v_r_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3165_ = l_Lean_ConstantInfo_isUnsafe(v_x_3164_);
    crate::leanh::lean_dec_ref(v_x_3164_);
    v_r_3166_ = crate::leanh::lean_box((v_res_3165_) as usize);
    return v_r_3166_;
}
pub unsafe fn l_Lean_ConstantInfo_isPartial(mut v_x_3167_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3167_) == 1 {
        let mut v_val_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_safety_3169_: u8 = 0;
        let mut v___x_3170_: u8 = 0;
        let mut v___x_3171_: u8 = 0;
        v_val_3168_ = crate::leanh::lean_ctor_get(v_x_3167_, 0);
        v_safety_3169_ = crate::leanh::lean_ctor_get_uint8(
            v_val_3168_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        );
        v___x_3170_ = 2;
        v___x_3171_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3169_, v___x_3170_);
        return v___x_3171_;
    } else {
        let mut v___x_3172_: u8 = 0;
        v___x_3172_ = 0;
        return v___x_3172_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_isPartial___boxed(
    mut v_x_3173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3174_: u8 = 0;
    let mut v_r_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_Lean_ConstantInfo_isPartial(v_x_3173_);
    crate::leanh::lean_dec_ref(v_x_3173_);
    v_r_3175_ = crate::leanh::lean_box((v_res_3174_) as usize);
    return v_r_3175_;
}
pub unsafe fn l_Lean_ConstantInfo_name(
    mut v_d_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3177_ = l_Lean_ConstantInfo_toConstantVal(v_d_3176_);
    v_name_3178_ = crate::leanh::lean_ctor_get(v___x_3177_, 0);
    crate::leanh::lean_inc(v_name_3178_);
    crate::leanh::lean_dec_ref(v___x_3177_);
    return v_name_3178_;
}
pub unsafe fn l_Lean_ConstantInfo_name___boxed(
    mut v_d_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3180_ = l_Lean_ConstantInfo_name(v_d_3179_);
    crate::leanh::lean_dec_ref(v_d_3179_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_ConstantInfo_levelParams(
    mut v_d_3181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3182_ = l_Lean_ConstantInfo_toConstantVal(v_d_3181_);
    v_levelParams_3183_ = crate::leanh::lean_ctor_get(v___x_3182_, 1);
    crate::leanh::lean_inc(v_levelParams_3183_);
    crate::leanh::lean_dec_ref(v___x_3182_);
    return v_levelParams_3183_;
}
pub unsafe fn l_Lean_ConstantInfo_levelParams___boxed(
    mut v_d_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3185_ = l_Lean_ConstantInfo_levelParams(v_d_3184_);
    crate::leanh::lean_dec_ref(v_d_3184_);
    return v_res_3185_;
}
pub unsafe fn l_Lean_ConstantInfo_numLevelParams(
    mut v_d_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3187_ = l_Lean_ConstantInfo_levelParams(v_d_3186_);
    v___x_3188_ = l_List_lengthTR___redArg(v___x_3187_);
    crate::leanh::lean_dec(v___x_3187_);
    return v___x_3188_;
}
pub unsafe fn l_Lean_ConstantInfo_numLevelParams___boxed(
    mut v_d_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3190_ = l_Lean_ConstantInfo_numLevelParams(v_d_3189_);
    crate::leanh::lean_dec_ref(v_d_3189_);
    return v_res_3190_;
}
pub unsafe fn l_Lean_ConstantInfo_type(
    mut v_d_3191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3192_ = l_Lean_ConstantInfo_toConstantVal(v_d_3191_);
    v_type_3193_ = crate::leanh::lean_ctor_get(v___x_3192_, 2);
    crate::leanh::lean_inc_ref(v_type_3193_);
    crate::leanh::lean_dec_ref(v___x_3192_);
    return v_type_3193_;
}
pub unsafe fn l_Lean_ConstantInfo_type___boxed(
    mut v_d_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_Lean_ConstantInfo_type(v_d_3194_);
    crate::leanh::lean_dec_ref(v_d_3194_);
    return v_res_3195_;
}
pub unsafe fn l_Lean_ConstantInfo_value_x3f(
    mut v_info_3196_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_3197_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v_value_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_val_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut v_val_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_info_3196_) {
                1 => {
                    v_val_3198_ = crate::leanh::lean_ctor_get(v_info_3196_, 0);
                    v_isSharedCheck_3206_ = (!crate::leanh::lean_is_exclusive(v_info_3196_)) as u8;
                    if v_isSharedCheck_3206_ == 0 {
                        v___x_3200_ = v_info_3196_;
                        v_isShared_3201_ = v_isSharedCheck_3206_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3198_);
                        crate::leanh::lean_dec(v_info_3196_);
                        v___x_3200_ = crate::leanh::lean_box(0);
                        v_isShared_3201_ = v_isSharedCheck_3206_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_val_3207_ = crate::leanh::lean_ctor_get(v_info_3196_, 0);
                    v_isSharedCheck_3216_ = (!crate::leanh::lean_is_exclusive(v_info_3196_)) as u8;
                    if v_isSharedCheck_3216_ == 0 {
                        v___x_3209_ = v_info_3196_;
                        v_isShared_3210_ = v_isSharedCheck_3216_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3207_);
                        crate::leanh::lean_dec(v_info_3196_);
                        v___x_3209_ = crate::leanh::lean_box(0);
                        v_isShared_3210_ = v_isSharedCheck_3216_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_val_3217_ = crate::leanh::lean_ctor_get(v_info_3196_, 0);
                    v_isSharedCheck_3226_ = (!crate::leanh::lean_is_exclusive(v_info_3196_)) as u8;
                    if v_isSharedCheck_3226_ == 0 {
                        v___x_3219_ = v_info_3196_;
                        v_isShared_3220_ = v_isSharedCheck_3226_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3217_);
                        crate::leanh::lean_dec(v_info_3196_);
                        v___x_3219_ = crate::leanh::lean_box(0);
                        v_isShared_3220_ = v_isSharedCheck_3226_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_info_3196_);
                    v___x_3227_ = crate::leanh::lean_box(0);
                    return v___x_3227_;
                }
            },
            1 => {
                v_value_3202_ = crate::leanh::lean_ctor_get(v_val_3198_, 1);
                crate::leanh::lean_inc_ref(v_value_3202_);
                crate::leanh::lean_dec_ref(v_val_3198_);
                if v_isShared_3201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3200_, 0, v_value_3202_);
                    v___x_3204_ = v___x_3200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_value_3202_);
                    v___x_3204_ = v_reuseFailAlloc_3205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3204_;
            }
            3 => {
                if v_allowOpaque_3197_ == 0 {
                    crate::leanh::lean_del_object(v___x_3209_);
                    crate::leanh::lean_dec_ref(v_val_3207_);
                    v___x_3211_ = crate::leanh::lean_box(0);
                    return v___x_3211_;
                } else {
                    v_value_3212_ = crate::leanh::lean_ctor_get(v_val_3207_, 1);
                    crate::leanh::lean_inc_ref(v_value_3212_);
                    crate::leanh::lean_dec_ref(v_val_3207_);
                    if v_isShared_3210_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3209_, 1);
                        crate::leanh::lean_ctor_set(v___x_3209_, 0, v_value_3212_);
                        v___x_3214_ = v___x_3209_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3215_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_value_3212_);
                        v___x_3214_ = v_reuseFailAlloc_3215_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3214_;
            }
            5 => {
                if v_allowOpaque_3197_ == 0 {
                    crate::leanh::lean_del_object(v___x_3219_);
                    crate::leanh::lean_dec_ref(v_val_3217_);
                    v___x_3221_ = crate::leanh::lean_box(0);
                    return v___x_3221_;
                } else {
                    v_value_3222_ = crate::leanh::lean_ctor_get(v_val_3217_, 1);
                    crate::leanh::lean_inc_ref(v_value_3222_);
                    crate::leanh::lean_dec_ref(v_val_3217_);
                    if v_isShared_3220_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3219_, 1);
                        crate::leanh::lean_ctor_set(v___x_3219_, 0, v_value_3222_);
                        v___x_3224_ = v___x_3219_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_value_3222_);
                        v___x_3224_ = v_reuseFailAlloc_3225_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ConstantInfo_value_x3f___boxed(
    mut v_info_3228_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowOpaque_boxed_3230_: u8 = 0;
    let mut v_res_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_3230_ = (crate::leanh::lean_unbox(v_allowOpaque_3229_) as u8);
    v_res_3231_ = l_Lean_ConstantInfo_value_x3f(v_info_3228_, v_allowOpaque_boxed_3230_);
    return v_res_3231_;
}
pub unsafe fn l_Lean_ConstantInfo_hasValue(
    mut v_info_3232_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_3233_: u8,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_info_3232_) {
        1 => {
            let mut v___x_3234_: u8 = 0;
            v___x_3234_ = 1;
            return v___x_3234_;
        }
        2 => {
            return v_allowOpaque_3233_;
        }
        3 => {
            return v_allowOpaque_3233_;
        }
        _ => {
            let mut v___x_3235_: u8 = 0;
            v___x_3235_ = 0;
            return v___x_3235_;
        }
    }
}
pub unsafe fn l_Lean_ConstantInfo_hasValue___boxed(
    mut v_info_3236_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowOpaque_boxed_3238_: u8 = 0;
    let mut v_res_3239_: u8 = 0;
    let mut v_r_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_3238_ = (crate::leanh::lean_unbox(v_allowOpaque_3237_) as u8);
    v_res_3239_ = l_Lean_ConstantInfo_hasValue(v_info_3236_, v_allowOpaque_boxed_3238_);
    crate::leanh::lean_dec_ref(v_info_3236_);
    v_r_3240_ = crate::leanh::lean_box((v_res_3239_) as usize);
    return v_r_3240_;
}
pub unsafe fn l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(
    mut v_msg_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Lean_instInhabitedExpr;
    v___x_3243_ = lean_panic_fn_borrowed(v___x_3242_, v_msg_3241_);
    return v___x_3243_;
}
pub unsafe fn _init_l_Lean_ConstantInfo_value_x21___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ = l_Lean_ConstantInfo_value_x21___closed__1;
    v___x_3247_ = crate::leanh::lean_unsigned_to_nat(62);
    v___x_3248_ = crate::leanh::lean_unsigned_to_nat(508);
    v___x_3249_ = l_Lean_ConstantInfo_value_x21___closed__0;
    v___x_3250_ = l_Lean_Declaration_definitionVal_x21___closed__0;
    v___x_3251_ = l_mkPanicMessageWithDecl(
        v___x_3250_,
        v___x_3249_,
        v___x_3248_,
        v___x_3247_,
        v___x_3246_,
    );
    return v___x_3251_;
}
pub unsafe fn _init_l_Lean_ConstantInfo_value_x21___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = l_Lean_ConstantInfo_value_x21___closed__1;
    v___x_3253_ = crate::leanh::lean_unsigned_to_nat(62);
    v___x_3254_ = crate::leanh::lean_unsigned_to_nat(509);
    v___x_3255_ = l_Lean_ConstantInfo_value_x21___closed__0;
    v___x_3256_ = l_Lean_Declaration_definitionVal_x21___closed__0;
    v___x_3257_ = l_mkPanicMessageWithDecl(
        v___x_3256_,
        v___x_3255_,
        v___x_3254_,
        v___x_3253_,
        v___x_3252_,
    );
    return v___x_3257_;
}
pub unsafe fn l_Lean_ConstantInfo_value_x21(
    mut v_info_3260_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_3261_: u8,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_info_3260_) {
        1 => {
            let mut v_val_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3262_ = crate::leanh::lean_ctor_get(v_info_3260_, 0);
            v_value_3263_ = crate::leanh::lean_ctor_get(v_val_3262_, 1);
            crate::leanh::lean_inc_ref(v_value_3263_);
            return v_value_3263_;
        }
        2 => {
            if v_allowOpaque_3261_ == 0 {
                let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3264_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_ConstantInfo_value_x21___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_ConstantInfo_value_x21___closed__2_once),
                    _init_l_Lean_ConstantInfo_value_x21___closed__2,
                );
                v___x_3265_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_3264_);
                return v___x_3265_;
            } else {
                let mut v_val_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_value_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_val_3266_ = crate::leanh::lean_ctor_get(v_info_3260_, 0);
                v_value_3267_ = crate::leanh::lean_ctor_get(v_val_3266_, 1);
                crate::leanh::lean_inc_ref(v_value_3267_);
                return v_value_3267_;
            }
        }
        3 => {
            if v_allowOpaque_3261_ == 0 {
                let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3268_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_ConstantInfo_value_x21___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_ConstantInfo_value_x21___closed__3_once),
                    _init_l_Lean_ConstantInfo_value_x21___closed__3,
                );
                v___x_3269_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_3268_);
                return v___x_3269_;
            } else {
                let mut v_val_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_value_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_val_3270_ = crate::leanh::lean_ctor_get(v_info_3260_, 0);
                v_value_3271_ = crate::leanh::lean_ctor_get(v_val_3270_, 1);
                crate::leanh::lean_inc_ref(v_value_3271_);
                return v_value_3271_;
            }
        }
        _ => {
            let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3278_: u8 = 0;
            let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3272_ = l_Lean_Declaration_definitionVal_x21___closed__0;
            v___x_3273_ = l_Lean_ConstantInfo_value_x21___closed__0;
            v___x_3274_ = crate::leanh::lean_unsigned_to_nat(510);
            v___x_3275_ = crate::leanh::lean_unsigned_to_nat(31);
            v___x_3276_ = l_Lean_ConstantInfo_value_x21___closed__4;
            v___x_3277_ = l_Lean_ConstantInfo_name(v_info_3260_);
            v___x_3278_ = 1;
            v___x_3279_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v___x_3277_,
                v___x_3278_,
            );
            v___x_3280_ = lean_string_append(v___x_3276_, v___x_3279_);
            crate::leanh::lean_dec_ref(v___x_3279_);
            v___x_3281_ = l_Lean_ConstantInfo_value_x21___closed__5;
            v___x_3282_ = lean_string_append(v___x_3280_, v___x_3281_);
            v___x_3283_ = l_mkPanicMessageWithDecl(
                v___x_3272_,
                v___x_3273_,
                v___x_3274_,
                v___x_3275_,
                v___x_3282_,
            );
            crate::leanh::lean_dec_ref(v___x_3282_);
            v___x_3284_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_3283_);
            return v___x_3284_;
        }
    }
}
pub unsafe fn l_Lean_ConstantInfo_value_x21___boxed(
    mut v_info_3285_: *mut crate::leanh::LeanObject,
    mut v_allowOpaque_3286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowOpaque_boxed_3287_: u8 = 0;
    let mut v_res_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowOpaque_boxed_3287_ = (crate::leanh::lean_unbox(v_allowOpaque_3286_) as u8);
    v_res_3288_ = l_Lean_ConstantInfo_value_x21(v_info_3285_, v_allowOpaque_boxed_3287_);
    crate::leanh::lean_dec_ref(v_info_3285_);
    return v_res_3288_;
}
pub unsafe fn l_Lean_ConstantInfo_hints(
    mut v_x_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3289_) == 1 {
        let mut v_val_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_hints_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3290_ = crate::leanh::lean_ctor_get(v_x_3289_, 0);
        v_hints_3291_ = crate::leanh::lean_ctor_get(v_val_3290_, 2);
        crate::leanh::lean_inc(v_hints_3291_);
        return v_hints_3291_;
    } else {
        let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3292_ = crate::leanh::lean_box(0);
        return v___x_3292_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_hints___boxed(
    mut v_x_3293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3294_ = l_Lean_ConstantInfo_hints(v_x_3293_);
    crate::leanh::lean_dec_ref(v_x_3293_);
    return v_res_3294_;
}
pub unsafe fn l_Lean_ConstantInfo_isCtor(mut v_x_3295_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3295_) == 6 {
        let mut v___x_3296_: u8 = 0;
        v___x_3296_ = 1;
        return v___x_3296_;
    } else {
        let mut v___x_3297_: u8 = 0;
        v___x_3297_ = 0;
        return v___x_3297_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_isCtor___boxed(
    mut v_x_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3299_: u8 = 0;
    let mut v_r_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3299_ = l_Lean_ConstantInfo_isCtor(v_x_3298_);
    crate::leanh::lean_dec_ref(v_x_3298_);
    v_r_3300_ = crate::leanh::lean_box((v_res_3299_) as usize);
    return v_r_3300_;
}
pub unsafe fn l_Lean_ConstantInfo_isAxiom(mut v_x_3301_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3301_) == 0 {
        let mut v___x_3302_: u8 = 0;
        v___x_3302_ = 1;
        return v___x_3302_;
    } else {
        let mut v___x_3303_: u8 = 0;
        v___x_3303_ = 0;
        return v___x_3303_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_isAxiom___boxed(
    mut v_x_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3305_: u8 = 0;
    let mut v_r_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3305_ = l_Lean_ConstantInfo_isAxiom(v_x_3304_);
    crate::leanh::lean_dec_ref(v_x_3304_);
    v_r_3306_ = crate::leanh::lean_box((v_res_3305_) as usize);
    return v_r_3306_;
}
pub unsafe fn l_Lean_ConstantInfo_isInductive(mut v_x_3307_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3307_) == 5 {
        let mut v___x_3308_: u8 = 0;
        v___x_3308_ = 1;
        return v___x_3308_;
    } else {
        let mut v___x_3309_: u8 = 0;
        v___x_3309_ = 0;
        return v___x_3309_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_isInductive___boxed(
    mut v_x_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3311_: u8 = 0;
    let mut v_r_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3311_ = l_Lean_ConstantInfo_isInductive(v_x_3310_);
    crate::leanh::lean_dec_ref(v_x_3310_);
    v_r_3312_ = crate::leanh::lean_box((v_res_3311_) as usize);
    return v_r_3312_;
}
pub unsafe fn l_Lean_ConstantInfo_isDefinition(mut v_x_3313_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3313_) == 1 {
        let mut v___x_3314_: u8 = 0;
        v___x_3314_ = 1;
        return v___x_3314_;
    } else {
        let mut v___x_3315_: u8 = 0;
        v___x_3315_ = 0;
        return v___x_3315_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_isDefinition___boxed(
    mut v_x_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3317_: u8 = 0;
    let mut v_r_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3317_ = l_Lean_ConstantInfo_isDefinition(v_x_3316_);
    crate::leanh::lean_dec_ref(v_x_3316_);
    v_r_3318_ = crate::leanh::lean_box((v_res_3317_) as usize);
    return v_r_3318_;
}
pub unsafe fn l_Lean_ConstantInfo_isTheorem(mut v_x_3319_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3319_) == 2 {
        let mut v___x_3320_: u8 = 0;
        v___x_3320_ = 1;
        return v___x_3320_;
    } else {
        let mut v___x_3321_: u8 = 0;
        v___x_3321_ = 0;
        return v___x_3321_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_isTheorem___boxed(
    mut v_x_3322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3323_: u8 = 0;
    let mut v_r_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3323_ = l_Lean_ConstantInfo_isTheorem(v_x_3322_);
    crate::leanh::lean_dec_ref(v_x_3322_);
    v_r_3324_ = crate::leanh::lean_box((v_res_3323_) as usize);
    return v_r_3324_;
}
pub unsafe fn l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(
    mut v_msg_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Lean_instInhabitedInductiveVal_default;
    v___x_3327_ = lean_panic_fn_borrowed(v___x_3326_, v_msg_3325_);
    return v___x_3327_;
}
pub unsafe fn _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3330_ = l_Lean_ConstantInfo_inductiveVal_x21___closed__1;
    v___x_3331_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_3332_ = crate::leanh::lean_unsigned_to_nat(538);
    v___x_3333_ = l_Lean_ConstantInfo_inductiveVal_x21___closed__0;
    v___x_3334_ = l_Lean_Declaration_definitionVal_x21___closed__0;
    v___x_3335_ = l_mkPanicMessageWithDecl(
        v___x_3334_,
        v___x_3333_,
        v___x_3332_,
        v___x_3331_,
        v___x_3330_,
    );
    return v___x_3335_;
}
pub unsafe fn l_Lean_ConstantInfo_inductiveVal_x21(
    mut v_x_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3336_) == 5 {
        let mut v_val_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3337_ = crate::leanh::lean_ctor_get(v_x_3336_, 0);
        crate::leanh::lean_inc_ref(v_val_3337_);
        return v_val_3337_;
    } else {
        let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3338_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_ConstantInfo_inductiveVal_x21___closed__2),
            core::ptr::addr_of_mut!(l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once),
            _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2,
        );
        v___x_3339_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_3338_);
        return v___x_3339_;
    }
}
pub unsafe fn l_Lean_ConstantInfo_inductiveVal_x21___boxed(
    mut v_x_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3341_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_3340_);
    crate::leanh::lean_dec_ref(v_x_3340_);
    return v_res_3341_;
}
pub unsafe fn l_Lean_ConstantInfo_all(
    mut v_x_3342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3342_) {
        5 => {
            let mut v_val_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_all_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3343_ = crate::leanh::lean_ctor_get(v_x_3342_, 0);
            v_all_3344_ = crate::leanh::lean_ctor_get(v_val_3343_, 3);
            crate::leanh::lean_inc(v_all_3344_);
            return v_all_3344_;
        }
        1 => {
            let mut v_val_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_all_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3345_ = crate::leanh::lean_ctor_get(v_x_3342_, 0);
            v_all_3346_ = crate::leanh::lean_ctor_get(v_val_3345_, 3);
            crate::leanh::lean_inc(v_all_3346_);
            return v_all_3346_;
        }
        2 => {
            let mut v_val_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_all_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3347_ = crate::leanh::lean_ctor_get(v_x_3342_, 0);
            v_all_3348_ = crate::leanh::lean_ctor_get(v_val_3347_, 2);
            crate::leanh::lean_inc(v_all_3348_);
            return v_all_3348_;
        }
        3 => {
            let mut v_val_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_all_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3349_ = crate::leanh::lean_ctor_get(v_x_3342_, 0);
            v_all_3350_ = crate::leanh::lean_ctor_get(v_val_3349_, 2);
            crate::leanh::lean_inc(v_all_3350_);
            return v_all_3350_;
        }
        _ => {
            let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3351_ = l_Lean_ConstantInfo_name(v_x_3342_);
            v___x_3352_ = crate::leanh::lean_box(0);
            v___x_3353_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3353_, 0, v___x_3351_);
            crate::leanh::lean_ctor_set(v___x_3353_, 1, v___x_3352_);
            return v___x_3353_;
        }
    }
}
pub unsafe fn l_Lean_ConstantInfo_all___boxed(
    mut v_x_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_ConstantInfo_all(v_x_3354_);
    crate::leanh::lean_dec_ref(v_x_3354_);
    return v_res_3355_;
}
pub unsafe fn l_Lean_mkRecName(
    mut v_declName_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3357_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0;
    v___x_3358_ = l_Lean_Name_str___override(v_declName_3356_, v___x_3357_);
    return v___x_3358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Declaration(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_instInhabitedReducibilityHints_default =
        _init_l_Lean_instInhabitedReducibilityHints_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedReducibilityHints_default);
    l_Lean_instInhabitedReducibilityHints = _init_l_Lean_instInhabitedReducibilityHints();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedReducibilityHints);
    l_Lean_instInhabitedConstantVal_default = _init_l_Lean_instInhabitedConstantVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstantVal_default);
    l_Lean_instInhabitedConstantVal = _init_l_Lean_instInhabitedConstantVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstantVal);
    l_Lean_instInhabitedAxiomVal_default = _init_l_Lean_instInhabitedAxiomVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedAxiomVal_default);
    l_Lean_instInhabitedAxiomVal = _init_l_Lean_instInhabitedAxiomVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedAxiomVal);
    l_Lean_instInhabitedDefinitionSafety_default =
        _init_l_Lean_instInhabitedDefinitionSafety_default();
    l_Lean_instInhabitedDefinitionSafety = _init_l_Lean_instInhabitedDefinitionSafety();
    l_Lean_instInhabitedDefinitionVal_default = _init_l_Lean_instInhabitedDefinitionVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDefinitionVal_default);
    l_Lean_instInhabitedDefinitionVal = _init_l_Lean_instInhabitedDefinitionVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDefinitionVal);
    l_Lean_instInhabitedTheoremVal_default = _init_l_Lean_instInhabitedTheoremVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedTheoremVal_default);
    l_Lean_instInhabitedTheoremVal = _init_l_Lean_instInhabitedTheoremVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedTheoremVal);
    l_Lean_instInhabitedOpaqueVal_default = _init_l_Lean_instInhabitedOpaqueVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedOpaqueVal_default);
    l_Lean_instInhabitedOpaqueVal = _init_l_Lean_instInhabitedOpaqueVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedOpaqueVal);
    l_Lean_instInhabitedConstructor_default = _init_l_Lean_instInhabitedConstructor_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstructor_default);
    l_Lean_instInhabitedConstructor = _init_l_Lean_instInhabitedConstructor();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstructor);
    l_Lean_instInhabitedInductiveType_default = _init_l_Lean_instInhabitedInductiveType_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedInductiveType_default);
    l_Lean_instInhabitedInductiveType = _init_l_Lean_instInhabitedInductiveType();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedInductiveType);
    l_Lean_instInhabitedDeclaration_default = _init_l_Lean_instInhabitedDeclaration_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclaration_default);
    l_Lean_instInhabitedDeclaration = _init_l_Lean_instInhabitedDeclaration();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedDeclaration);
    l_Lean_instInhabitedInductiveVal_default = _init_l_Lean_instInhabitedInductiveVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedInductiveVal_default);
    l_Lean_instInhabitedInductiveVal = _init_l_Lean_instInhabitedInductiveVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedInductiveVal);
    l_Lean_instInhabitedConstructorVal_default = _init_l_Lean_instInhabitedConstructorVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstructorVal_default);
    l_Lean_instInhabitedConstructorVal = _init_l_Lean_instInhabitedConstructorVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstructorVal);
    l_Lean_instInhabitedRecursorRule_default = _init_l_Lean_instInhabitedRecursorRule_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedRecursorRule_default);
    l_Lean_instInhabitedRecursorRule = _init_l_Lean_instInhabitedRecursorRule();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedRecursorRule);
    l_Lean_instInhabitedRecursorVal_default = _init_l_Lean_instInhabitedRecursorVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedRecursorVal_default);
    l_Lean_instInhabitedRecursorVal = _init_l_Lean_instInhabitedRecursorVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedRecursorVal);
    l_Lean_instInhabitedQuotKind_default = _init_l_Lean_instInhabitedQuotKind_default();
    l_Lean_instInhabitedQuotKind = _init_l_Lean_instInhabitedQuotKind();
    l_Lean_instInhabitedQuotVal_default = _init_l_Lean_instInhabitedQuotVal_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedQuotVal_default);
    l_Lean_instInhabitedQuotVal = _init_l_Lean_instInhabitedQuotVal();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedQuotVal);
    l_Lean_instInhabitedConstantInfo_default = _init_l_Lean_instInhabitedConstantInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstantInfo_default);
    l_Lean_instInhabitedConstantInfo = _init_l_Lean_instInhabitedConstantInfo();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedConstantInfo);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Declaration(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Declaration(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Declaration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Declaration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Declaration(builtin);
}
