// Lean compiler output
// Module: Lean.Elab.InfoTree.Types
// Imports: Lean.Data.DeclarationRange Lean.Data.OpenDecl Lean.Data.PPContext Lean.MetavarContext Lean.Environment Lean.Widget.Types
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Lean::Data::DeclarationRange::{
    initialize_Lean_Data_DeclarationRange, runtime_initialize_Lean_Data_DeclarationRange,
};
use crate::r#gen::Lean::Data::OpenDecl::{
    initialize_Lean_Data_OpenDecl, runtime_initialize_Lean_Data_OpenDecl,
};
use crate::r#gen::Lean::Data::PPContext::{
    initialize_Lean_Data_PPContext, runtime_initialize_Lean_Data_PPContext,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArray_default;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    initialize_Lean_Environment, runtime_initialize_Lean_Environment,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::LocalContext::l_Lean_instInhabitedLocalContext_default;
use crate::r#gen::Lean::MetavarContext::{
    initialize_Lean_MetavarContext, runtime_initialize_Lean_MetavarContext,
};
use crate::r#gen::Lean::Widget::Types::{
    initialize_Lean_Widget_Types, runtime_initialize_Lean_Widget_Types,
};
use crate::ffi::lean_nat_to_int;
use crate::ffi::{lean_mk_empty_array_with_capacity, lean_nat_dec_le};
pub static l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedElabInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedElabInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedElabInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value:
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
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTermInfo_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTermInfo_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTermInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTermInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedPartialTermInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedPartialTermInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedCommandInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedCommandInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedFieldInfo_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedFieldInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedFieldInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedFieldInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTacticInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTacticInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedMacroExpansionInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedMacroExpansionInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__0_value: crate::leanh::LeanStringObject<
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 68, 111, 99, 69, 108, 97, 98, 75, 105, 110, 100,
        46, 114, 111, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__2_value: crate::leanh::LeanStringObject<
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 68, 111, 99, 69, 108, 97, 98, 75, 105, 110, 100,
        46, 99, 111, 100, 101, 66, 108, 111, 99, 107, 0,
    ],
};
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__4_value: crate::leanh::LeanStringObject<
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 68, 111, 99, 69, 108, 97, 98, 75, 105, 110, 100,
        46, 100, 105, 114, 101, 99, 116, 105, 118, 101, 0,
    ],
};
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__6_value: crate::leanh::LeanStringObject<
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 68, 111, 99, 69, 108, 97, 98, 75, 105, 110, 100,
        46, 99, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instReprDocElabKind___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_instReprDocElabKind_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instReprDocElabKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instReprDocElabKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedInfo_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfo: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoTree_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoTree: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorIdx(
    mut v_x_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_665_) {
        0 => {
            let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_666_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_666_;
        }
        1 => {
            let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_667_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_667_;
        }
        _ => {
            let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_668_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_668_;
        }
    }
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorIdx___boxed(
    mut v_x_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Lean_Elab_PartialContextInfo_ctorIdx(v_x_669_);
    crate::leanh::lean_dec_ref(v_x_669_);
    return v_res_670_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorElim___redArg(
    mut v_t_671_: *mut crate::leanh::LeanObject,
    mut v_k_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_671_) == 1 {
        let mut v_parentDecl_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_parentDecl_673_ = crate::leanh::lean_ctor_get(v_t_671_, 0);
        crate::leanh::lean_inc(v_parentDecl_673_);
        crate::leanh::lean_dec_ref_known(v_t_671_, 1);
        v___x_674_ = crate::leanh::lean_apply_1(v_k_672_, v_parentDecl_673_);
        return v___x_674_;
    } else {
        let mut v_info_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_info_675_ = crate::leanh::lean_ctor_get(v_t_671_, 0);
        crate::leanh::lean_inc_ref(v_info_675_);
        crate::leanh::lean_dec_ref(v_t_671_);
        v___x_676_ = crate::leanh::lean_apply_1(v_k_672_, v_info_675_);
        return v___x_676_;
    }
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorElim(
    mut v_motive_677_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_678_: *mut crate::leanh::LeanObject,
    mut v_t_679_: *mut crate::leanh::LeanObject,
    mut v_h_680_: *mut crate::leanh::LeanObject,
    mut v_k_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_679_, v_k_681_);
    return v___x_682_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorElim___boxed(
    mut v_motive_683_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_684_: *mut crate::leanh::LeanObject,
    mut v_t_685_: *mut crate::leanh::LeanObject,
    mut v_h_686_: *mut crate::leanh::LeanObject,
    mut v_k_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_Elab_PartialContextInfo_ctorElim(
        v_motive_683_,
        v_ctorIdx_684_,
        v_t_685_,
        v_h_686_,
        v_k_687_,
    );
    crate::leanh::lean_dec(v_ctorIdx_684_);
    return v_res_688_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_commandCtx_elim___redArg(
    mut v_t_689_: *mut crate::leanh::LeanObject,
    mut v_commandCtx_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_689_, v_commandCtx_690_);
    return v___x_691_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_commandCtx_elim(
    mut v_motive_692_: *mut crate::leanh::LeanObject,
    mut v_t_693_: *mut crate::leanh::LeanObject,
    mut v_h_694_: *mut crate::leanh::LeanObject,
    mut v_commandCtx_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_693_, v_commandCtx_695_);
    return v___x_696_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim___redArg(
    mut v_t_697_: *mut crate::leanh::LeanObject,
    mut v_parentDeclCtx_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_697_, v_parentDeclCtx_698_);
    return v___x_699_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim(
    mut v_motive_700_: *mut crate::leanh::LeanObject,
    mut v_t_701_: *mut crate::leanh::LeanObject,
    mut v_h_702_: *mut crate::leanh::LeanObject,
    mut v_parentDeclCtx_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_701_, v_parentDeclCtx_703_);
    return v___x_704_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim___redArg(
    mut v_t_705_: *mut crate::leanh::LeanObject,
    mut v_autoImplicitCtx_706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_707_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_705_, v_autoImplicitCtx_706_);
    return v___x_707_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim(
    mut v_motive_708_: *mut crate::leanh::LeanObject,
    mut v_t_709_: *mut crate::leanh::LeanObject,
    mut v_h_710_: *mut crate::leanh::LeanObject,
    mut v_autoImplicitCtx_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_709_, v_autoImplicitCtx_711_);
    return v___x_712_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = crate::leanh::lean_box(0);
    v___x_722_ = l_Lean_Elab_instInhabitedTermInfo_default___closed__1;
    v___x_723_ = l_Lean_Expr_const___override(v___x_722_, v___x_721_);
    return v___x_723_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = 0;
    v___x_725_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2,
    );
    v___x_726_ = crate::leanh::lean_box(0);
    v___x_727_ = l_Lean_instInhabitedLocalContext_default;
    v___x_728_ = l_Lean_Elab_instInhabitedElabInfo_default;
    v___x_729_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_729_, 0, v___x_728_);
    crate::leanh::lean_ctor_set(v___x_729_, 1, v___x_727_);
    crate::leanh::lean_ctor_set(v___x_729_, 2, v___x_726_);
    crate::leanh::lean_ctor_set(v___x_729_, 3, v___x_725_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_729_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_724_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_729_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v___x_724_,
    );
    return v___x_729_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_730_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__3_once),
        _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3,
    );
    return v___x_730_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lean_Elab_instInhabitedTermInfo_default;
    return v___x_731_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = crate::leanh::lean_box(0);
    v___x_733_ = l_Lean_instInhabitedLocalContext_default;
    v___x_734_ = l_Lean_Elab_instInhabitedElabInfo_default;
    v___x_735_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_735_, 0, v___x_734_);
    crate::leanh::lean_ctor_set(v___x_735_, 1, v___x_733_);
    crate::leanh::lean_ctor_set(v___x_735_, 2, v___x_732_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialTermInfo_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0,
    );
    return v___x_736_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialTermInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_Elab_instInhabitedPartialTermInfo_default;
    return v___x_737_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorIdx(
    mut v_x_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_740_) {
        0 => {
            let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_741_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_741_;
        }
        1 => {
            let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_742_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_742_;
        }
        2 => {
            let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_743_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_743_;
        }
        3 => {
            let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_744_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_744_;
        }
        4 => {
            let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_745_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_745_;
        }
        5 => {
            let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_746_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_746_;
        }
        6 => {
            let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_747_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_747_;
        }
        7 => {
            let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_748_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_748_;
        }
        _ => {
            let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_749_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_749_;
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorIdx___boxed(
    mut v_x_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Lean_Elab_CompletionInfo_ctorIdx(v_x_750_);
    crate::leanh::lean_dec_ref(v_x_750_);
    return v_res_751_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorElim___redArg(
    mut v_t_752_: *mut crate::leanh::LeanObject,
    mut v_k_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_752_) {
        0 => {
            let mut v_termInfo_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedType_x3f_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_termInfo_754_ = crate::leanh::lean_ctor_get(v_t_752_, 0);
            crate::leanh::lean_inc_ref(v_termInfo_754_);
            v_expectedType_x3f_755_ = crate::leanh::lean_ctor_get(v_t_752_, 1);
            crate::leanh::lean_inc(v_expectedType_x3f_755_);
            crate::leanh::lean_dec_ref_known(v_t_752_, 2);
            v___x_756_ =
                crate::leanh::lean_apply_2(v_k_753_, v_termInfo_754_, v_expectedType_x3f_755_);
            return v___x_756_;
        }
        1 => {
            let mut v_stx_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_danglingDot_759_: u8 = 0;
            let mut v_lctx_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedType_x3f_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_stx_757_ = crate::leanh::lean_ctor_get(v_t_752_, 0);
            crate::leanh::lean_inc(v_stx_757_);
            v_id_758_ = crate::leanh::lean_ctor_get(v_t_752_, 1);
            crate::leanh::lean_inc(v_id_758_);
            v_danglingDot_759_ = crate::leanh::lean_ctor_get_uint8(
                v_t_752_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
            );
            v_lctx_760_ = crate::leanh::lean_ctor_get(v_t_752_, 2);
            crate::leanh::lean_inc_ref(v_lctx_760_);
            v_expectedType_x3f_761_ = crate::leanh::lean_ctor_get(v_t_752_, 3);
            crate::leanh::lean_inc(v_expectedType_x3f_761_);
            crate::leanh::lean_dec_ref_known(v_t_752_, 4);
            v___x_762_ = crate::leanh::lean_box((v_danglingDot_759_) as usize);
            v___x_763_ = crate::leanh::lean_apply_5(
                v_k_753_,
                v_stx_757_,
                v_id_758_,
                v___x_762_,
                v_lctx_760_,
                v_expectedType_x3f_761_,
            );
            return v___x_763_;
        }
        2 => {
            let mut v_stx_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lctx_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedType_x3f_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_stx_764_ = crate::leanh::lean_ctor_get(v_t_752_, 0);
            crate::leanh::lean_inc(v_stx_764_);
            v_id_765_ = crate::leanh::lean_ctor_get(v_t_752_, 1);
            crate::leanh::lean_inc(v_id_765_);
            v_lctx_766_ = crate::leanh::lean_ctor_get(v_t_752_, 2);
            crate::leanh::lean_inc_ref(v_lctx_766_);
            v_expectedType_x3f_767_ = crate::leanh::lean_ctor_get(v_t_752_, 3);
            crate::leanh::lean_inc(v_expectedType_x3f_767_);
            crate::leanh::lean_dec_ref_known(v_t_752_, 4);
            v___x_768_ = crate::leanh::lean_apply_4(
                v_k_753_,
                v_stx_764_,
                v_id_765_,
                v_lctx_766_,
                v_expectedType_x3f_767_,
            );
            return v___x_768_;
        }
        3 => {
            let mut v_stx_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_lctx_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_structName_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_stx_769_ = crate::leanh::lean_ctor_get(v_t_752_, 0);
            crate::leanh::lean_inc(v_stx_769_);
            v_id_770_ = crate::leanh::lean_ctor_get(v_t_752_, 1);
            crate::leanh::lean_inc(v_id_770_);
            v_lctx_771_ = crate::leanh::lean_ctor_get(v_t_752_, 2);
            crate::leanh::lean_inc_ref(v_lctx_771_);
            v_structName_772_ = crate::leanh::lean_ctor_get(v_t_752_, 3);
            crate::leanh::lean_inc(v_structName_772_);
            crate::leanh::lean_dec_ref_known(v_t_752_, 4);
            v___x_773_ = crate::leanh::lean_apply_4(
                v_k_753_,
                v_stx_769_,
                v_id_770_,
                v_lctx_771_,
                v_structName_772_,
            );
            return v___x_773_;
        }
        6 => {
            let mut v_stx_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_partialId_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_stx_774_ = crate::leanh::lean_ctor_get(v_t_752_, 0);
            crate::leanh::lean_inc(v_stx_774_);
            v_partialId_775_ = crate::leanh::lean_ctor_get(v_t_752_, 1);
            crate::leanh::lean_inc(v_partialId_775_);
            crate::leanh::lean_dec_ref_known(v_t_752_, 2);
            v___x_776_ = crate::leanh::lean_apply_2(v_k_753_, v_stx_774_, v_partialId_775_);
            return v___x_776_;
        }
        7 => {
            let mut v_stx_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_x3f_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_danglingDot_779_: u8 = 0;
            let mut v_scopeNames_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_stx_777_ = crate::leanh::lean_ctor_get(v_t_752_, 0);
            crate::leanh::lean_inc(v_stx_777_);
            v_id_x3f_778_ = crate::leanh::lean_ctor_get(v_t_752_, 1);
            crate::leanh::lean_inc(v_id_x3f_778_);
            v_danglingDot_779_ = crate::leanh::lean_ctor_get_uint8(
                v_t_752_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_scopeNames_780_ = crate::leanh::lean_ctor_get(v_t_752_, 2);
            crate::leanh::lean_inc(v_scopeNames_780_);
            crate::leanh::lean_dec_ref_known(v_t_752_, 3);
            v___x_781_ = crate::leanh::lean_box((v_danglingDot_779_) as usize);
            v___x_782_ = crate::leanh::lean_apply_4(
                v_k_753_,
                v_stx_777_,
                v_id_x3f_778_,
                v___x_781_,
                v_scopeNames_780_,
            );
            return v___x_782_;
        }
        _ => {
            let mut v_stx_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_stx_783_ = crate::leanh::lean_ctor_get(v_t_752_, 0);
            crate::leanh::lean_inc(v_stx_783_);
            crate::leanh::lean_dec_ref(v_t_752_);
            v___x_784_ = crate::leanh::lean_apply_1(v_k_753_, v_stx_783_);
            return v___x_784_;
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorElim(
    mut v_motive_785_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_786_: *mut crate::leanh::LeanObject,
    mut v_t_787_: *mut crate::leanh::LeanObject,
    mut v_h_788_: *mut crate::leanh::LeanObject,
    mut v_k_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_787_, v_k_789_);
    return v___x_790_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorElim___boxed(
    mut v_motive_791_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_792_: *mut crate::leanh::LeanObject,
    mut v_t_793_: *mut crate::leanh::LeanObject,
    mut v_h_794_: *mut crate::leanh::LeanObject,
    mut v_k_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_796_ = l_Lean_Elab_CompletionInfo_ctorElim(
        v_motive_791_,
        v_ctorIdx_792_,
        v_t_793_,
        v_h_794_,
        v_k_795_,
    );
    crate::leanh::lean_dec(v_ctorIdx_792_);
    return v_res_796_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dot_elim___redArg(
    mut v_t_797_: *mut crate::leanh::LeanObject,
    mut v_dot_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_797_, v_dot_798_);
    return v___x_799_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dot_elim(
    mut v_motive_800_: *mut crate::leanh::LeanObject,
    mut v_t_801_: *mut crate::leanh::LeanObject,
    mut v_h_802_: *mut crate::leanh::LeanObject,
    mut v_dot_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_801_, v_dot_803_);
    return v___x_804_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_id_elim___redArg(
    mut v_t_805_: *mut crate::leanh::LeanObject,
    mut v_id_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_805_, v_id_806_);
    return v___x_807_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_id_elim(
    mut v_motive_808_: *mut crate::leanh::LeanObject,
    mut v_t_809_: *mut crate::leanh::LeanObject,
    mut v_h_810_: *mut crate::leanh::LeanObject,
    mut v_id_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_809_, v_id_811_);
    return v___x_812_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dotId_elim___redArg(
    mut v_t_813_: *mut crate::leanh::LeanObject,
    mut v_dotId_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_813_, v_dotId_814_);
    return v___x_815_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dotId_elim(
    mut v_motive_816_: *mut crate::leanh::LeanObject,
    mut v_t_817_: *mut crate::leanh::LeanObject,
    mut v_h_818_: *mut crate::leanh::LeanObject,
    mut v_dotId_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_817_, v_dotId_819_);
    return v___x_820_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_fieldId_elim___redArg(
    mut v_t_821_: *mut crate::leanh::LeanObject,
    mut v_fieldId_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_821_, v_fieldId_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_fieldId_elim(
    mut v_motive_824_: *mut crate::leanh::LeanObject,
    mut v_t_825_: *mut crate::leanh::LeanObject,
    mut v_h_826_: *mut crate::leanh::LeanObject,
    mut v_fieldId_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_825_, v_fieldId_827_);
    return v___x_828_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_namespaceId_elim___redArg(
    mut v_t_829_: *mut crate::leanh::LeanObject,
    mut v_namespaceId_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_829_, v_namespaceId_830_);
    return v___x_831_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_namespaceId_elim(
    mut v_motive_832_: *mut crate::leanh::LeanObject,
    mut v_t_833_: *mut crate::leanh::LeanObject,
    mut v_h_834_: *mut crate::leanh::LeanObject,
    mut v_namespaceId_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_833_, v_namespaceId_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_option_elim___redArg(
    mut v_t_837_: *mut crate::leanh::LeanObject,
    mut v_option_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_837_, v_option_838_);
    return v___x_839_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_option_elim(
    mut v_motive_840_: *mut crate::leanh::LeanObject,
    mut v_t_841_: *mut crate::leanh::LeanObject,
    mut v_h_842_: *mut crate::leanh::LeanObject,
    mut v_option_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_841_, v_option_843_);
    return v___x_844_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_errorName_elim___redArg(
    mut v_t_845_: *mut crate::leanh::LeanObject,
    mut v_errorName_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_845_, v_errorName_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_errorName_elim(
    mut v_motive_848_: *mut crate::leanh::LeanObject,
    mut v_t_849_: *mut crate::leanh::LeanObject,
    mut v_h_850_: *mut crate::leanh::LeanObject,
    mut v_errorName_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_849_, v_errorName_851_);
    return v___x_852_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_endSection_elim___redArg(
    mut v_t_853_: *mut crate::leanh::LeanObject,
    mut v_endSection_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_853_, v_endSection_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_endSection_elim(
    mut v_motive_856_: *mut crate::leanh::LeanObject,
    mut v_t_857_: *mut crate::leanh::LeanObject,
    mut v_h_858_: *mut crate::leanh::LeanObject,
    mut v_endSection_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_857_, v_endSection_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_tactic_elim___redArg(
    mut v_t_861_: *mut crate::leanh::LeanObject,
    mut v_tactic_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_861_, v_tactic_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_tactic_elim(
    mut v_motive_864_: *mut crate::leanh::LeanObject,
    mut v_t_865_: *mut crate::leanh::LeanObject,
    mut v_h_866_: *mut crate::leanh::LeanObject,
    mut v_tactic_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_865_, v_tactic_867_);
    return v___x_868_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = crate::leanh::lean_box(0);
    v___x_870_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2,
    );
    v___x_871_ = l_Lean_instInhabitedLocalContext_default;
    v___x_872_ = crate::leanh::lean_box(0);
    v___x_873_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_873_, 0, v___x_872_);
    crate::leanh::lean_ctor_set(v___x_873_, 1, v___x_872_);
    crate::leanh::lean_ctor_set(v___x_873_, 2, v___x_871_);
    crate::leanh::lean_ctor_set(v___x_873_, 3, v___x_870_);
    crate::leanh::lean_ctor_set(v___x_873_, 4, v___x_869_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedFieldInfo_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedFieldInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedFieldInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0,
    );
    return v___x_874_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedFieldInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_Lean_Elab_instInhabitedFieldInfo_default;
    return v___x_875_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0,
    );
    v___x_878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_878_, 0, v___x_877_);
    return v___x_878_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1,
    );
    v___x_880_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_881_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_881_, 0, v___x_880_);
    crate::leanh::lean_ctor_set(v___x_881_, 1, v___x_880_);
    crate::leanh::lean_ctor_set(v___x_881_, 2, v___x_880_);
    crate::leanh::lean_ctor_set(v___x_881_, 3, v___x_880_);
    crate::leanh::lean_ctor_set(v___x_881_, 4, v___x_879_);
    crate::leanh::lean_ctor_set(v___x_881_, 5, v___x_879_);
    crate::leanh::lean_ctor_set(v___x_881_, 6, v___x_879_);
    crate::leanh::lean_ctor_set(v___x_881_, 7, v___x_879_);
    crate::leanh::lean_ctor_set(v___x_881_, 8, v___x_879_);
    crate::leanh::lean_ctor_set(v___x_881_, 9, v___x_879_);
    return v___x_881_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = crate::leanh::lean_box(0);
    v___x_883_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2,
    );
    v___x_884_ = l_Lean_Elab_instInhabitedElabInfo_default;
    v___x_885_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_885_, 0, v___x_884_);
    crate::leanh::lean_ctor_set(v___x_885_, 1, v___x_883_);
    crate::leanh::lean_ctor_set(v___x_885_, 2, v___x_882_);
    crate::leanh::lean_ctor_set(v___x_885_, 3, v___x_883_);
    crate::leanh::lean_ctor_set(v___x_885_, 4, v___x_882_);
    return v___x_885_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3,
    );
    return v___x_886_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = l_Lean_Elab_instInhabitedTacticInfo_default;
    return v___x_887_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = crate::leanh::lean_box(0);
    v___x_889_ = l_Lean_instInhabitedLocalContext_default;
    v___x_890_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_890_, 0, v___x_889_);
    crate::leanh::lean_ctor_set(v___x_890_, 1, v___x_888_);
    crate::leanh::lean_ctor_set(v___x_890_, 2, v___x_888_);
    return v___x_890_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once
        ),
        _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0,
    );
    return v___x_891_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedMacroExpansionInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_892_ = l_Lean_Elab_instInhabitedMacroExpansionInfo_default;
    return v___x_892_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorIdx(mut v_x_893_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_893_ {
        0 => {
            let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_894_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_894_;
        }
        1 => {
            let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_895_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_895_;
        }
        2 => {
            let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_896_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_896_;
        }
        _ => {
            let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_897_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_897_;
        }
    }
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorIdx___boxed(
    mut v_x_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_899_: u8 = 0;
    let mut v_res_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_899_ = (crate::leanh::lean_unbox(v_x_898_) as u8);
    v_res_900_ = l_Lean_Elab_DocElabKind_ctorIdx(v_x_boxed_899_);
    return v_res_900_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_toCtorIdx(mut v_x_901_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_902_ = l_Lean_Elab_DocElabKind_ctorIdx(v_x_901_);
    return v___x_902_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_toCtorIdx___boxed(
    mut v_x_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_904_: u8 = 0;
    let mut v_res_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_904_ = (crate::leanh::lean_unbox(v_x_903_) as u8);
    v_res_905_ = l_Lean_Elab_DocElabKind_toCtorIdx(v_x_4__boxed_904_);
    return v_res_905_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim___redArg(
    mut v_k_906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_906_);
    return v_k_906_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim___redArg___boxed(
    mut v_k_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_908_ = l_Lean_Elab_DocElabKind_ctorElim___redArg(v_k_907_);
    crate::leanh::lean_dec(v_k_907_);
    return v_res_908_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim(
    mut v_motive_909_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_910_: *mut crate::leanh::LeanObject,
    mut v_t_911_: u8,
    mut v_h_912_: *mut crate::leanh::LeanObject,
    mut v_k_913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_913_);
    return v_k_913_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim___boxed(
    mut v_motive_914_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_915_: *mut crate::leanh::LeanObject,
    mut v_t_916_: *mut crate::leanh::LeanObject,
    mut v_h_917_: *mut crate::leanh::LeanObject,
    mut v_k_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_919_: u8 = 0;
    let mut v_res_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_919_ = (crate::leanh::lean_unbox(v_t_916_) as u8);
    v_res_920_ = l_Lean_Elab_DocElabKind_ctorElim(
        v_motive_914_,
        v_ctorIdx_915_,
        v_t_boxed_919_,
        v_h_917_,
        v_k_918_,
    );
    crate::leanh::lean_dec(v_k_918_);
    crate::leanh::lean_dec(v_ctorIdx_915_);
    return v_res_920_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim___redArg(
    mut v_role_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_role_921_);
    return v_role_921_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim___redArg___boxed(
    mut v_role_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_923_ = l_Lean_Elab_DocElabKind_role_elim___redArg(v_role_922_);
    crate::leanh::lean_dec(v_role_922_);
    return v_res_923_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim(
    mut v_motive_924_: *mut crate::leanh::LeanObject,
    mut v_t_925_: u8,
    mut v_h_926_: *mut crate::leanh::LeanObject,
    mut v_role_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_role_927_);
    return v_role_927_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim___boxed(
    mut v_motive_928_: *mut crate::leanh::LeanObject,
    mut v_t_929_: *mut crate::leanh::LeanObject,
    mut v_h_930_: *mut crate::leanh::LeanObject,
    mut v_role_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_932_: u8 = 0;
    let mut v_res_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_932_ = (crate::leanh::lean_unbox(v_t_929_) as u8);
    v_res_933_ =
        l_Lean_Elab_DocElabKind_role_elim(v_motive_928_, v_t_boxed_932_, v_h_930_, v_role_931_);
    crate::leanh::lean_dec(v_role_931_);
    return v_res_933_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(
    mut v_codeBlock_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_codeBlock_934_);
    return v_codeBlock_934_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim___redArg___boxed(
    mut v_codeBlock_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_936_ = l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(v_codeBlock_935_);
    crate::leanh::lean_dec(v_codeBlock_935_);
    return v_res_936_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim(
    mut v_motive_937_: *mut crate::leanh::LeanObject,
    mut v_t_938_: u8,
    mut v_h_939_: *mut crate::leanh::LeanObject,
    mut v_codeBlock_940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_codeBlock_940_);
    return v_codeBlock_940_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim___boxed(
    mut v_motive_941_: *mut crate::leanh::LeanObject,
    mut v_t_942_: *mut crate::leanh::LeanObject,
    mut v_h_943_: *mut crate::leanh::LeanObject,
    mut v_codeBlock_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_945_: u8 = 0;
    let mut v_res_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_945_ = (crate::leanh::lean_unbox(v_t_942_) as u8);
    v_res_946_ = l_Lean_Elab_DocElabKind_codeBlock_elim(
        v_motive_941_,
        v_t_boxed_945_,
        v_h_943_,
        v_codeBlock_944_,
    );
    crate::leanh::lean_dec(v_codeBlock_944_);
    return v_res_946_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim___redArg(
    mut v_directive_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_directive_947_);
    return v_directive_947_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim___redArg___boxed(
    mut v_directive_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_949_ = l_Lean_Elab_DocElabKind_directive_elim___redArg(v_directive_948_);
    crate::leanh::lean_dec(v_directive_948_);
    return v_res_949_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim(
    mut v_motive_950_: *mut crate::leanh::LeanObject,
    mut v_t_951_: u8,
    mut v_h_952_: *mut crate::leanh::LeanObject,
    mut v_directive_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_directive_953_);
    return v_directive_953_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim___boxed(
    mut v_motive_954_: *mut crate::leanh::LeanObject,
    mut v_t_955_: *mut crate::leanh::LeanObject,
    mut v_h_956_: *mut crate::leanh::LeanObject,
    mut v_directive_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_958_: u8 = 0;
    let mut v_res_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_958_ = (crate::leanh::lean_unbox(v_t_955_) as u8);
    v_res_959_ = l_Lean_Elab_DocElabKind_directive_elim(
        v_motive_954_,
        v_t_boxed_958_,
        v_h_956_,
        v_directive_957_,
    );
    crate::leanh::lean_dec(v_directive_957_);
    return v_res_959_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim___redArg(
    mut v_command_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_command_960_);
    return v_command_960_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim___redArg___boxed(
    mut v_command_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Lean_Elab_DocElabKind_command_elim___redArg(v_command_961_);
    crate::leanh::lean_dec(v_command_961_);
    return v_res_962_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim(
    mut v_motive_963_: *mut crate::leanh::LeanObject,
    mut v_t_964_: u8,
    mut v_h_965_: *mut crate::leanh::LeanObject,
    mut v_command_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_command_966_);
    return v_command_966_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim___boxed(
    mut v_motive_967_: *mut crate::leanh::LeanObject,
    mut v_t_968_: *mut crate::leanh::LeanObject,
    mut v_h_969_: *mut crate::leanh::LeanObject,
    mut v_command_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_971_: u8 = 0;
    let mut v_res_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_971_ = (crate::leanh::lean_unbox(v_t_968_) as u8);
    v_res_972_ = l_Lean_Elab_DocElabKind_command_elim(
        v_motive_967_,
        v_t_boxed_971_,
        v_h_969_,
        v_command_970_,
    );
    crate::leanh::lean_dec(v_command_970_);
    return v_res_972_;
}
pub unsafe fn _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_986_ = lean_nat_to_int(v___x_985_);
    return v___x_986_;
}
pub unsafe fn _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_988_ = lean_nat_to_int(v___x_987_);
    return v___x_988_;
}
pub unsafe fn l_Lean_Elab_instReprDocElabKind_repr(
    mut v_x_989_: u8,
    mut v_prec_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: u8 = 0;
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u8 = 0;
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: u8 = 0;
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_989_ {
                0 => {
                    v___x_1019_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1020_ = lean_nat_dec_le(v___x_1019_, v_prec_990_);
                    if v___x_1020_ == 0 {
                        v___x_1021_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8,
                        );
                        v___y_992_ = v___x_1021_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1022_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9,
                        );
                        v___y_992_ = v___x_1022_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_1023_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1024_ = lean_nat_dec_le(v___x_1023_, v_prec_990_);
                    if v___x_1024_ == 0 {
                        v___x_1025_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8,
                        );
                        v___y_999_ = v___x_1025_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1026_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9,
                        );
                        v___y_999_ = v___x_1026_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_1027_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1028_ = lean_nat_dec_le(v___x_1027_, v_prec_990_);
                    if v___x_1028_ == 0 {
                        v___x_1029_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8,
                        );
                        v___y_1006_ = v___x_1029_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1030_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9,
                        );
                        v___y_1006_ = v___x_1030_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_1031_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1032_ = lean_nat_dec_le(v___x_1031_, v_prec_990_);
                    if v___x_1032_ == 0 {
                        v___x_1033_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__8_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8,
                        );
                        v___y_1013_ = v___x_1033_;
                        state = 4;
                        continue;
                    } else {
                        v___x_1034_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_instReprDocElabKind_repr___closed__9_once
                            ),
                            _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9,
                        );
                        v___y_1013_ = v___x_1034_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_993_ = l_Lean_Elab_instReprDocElabKind_repr___closed__1;
                crate::leanh::lean_inc(v___y_992_);
                v___x_994_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_994_, 0, v___y_992_);
                crate::leanh::lean_ctor_set(v___x_994_, 1, v___x_993_);
                v___x_995_ = 0;
                v___x_996_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_996_, 0, v___x_994_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_996_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_995_,
                );
                v___x_997_ = l_Repr_addAppParen(v___x_996_, v_prec_990_);
                return v___x_997_;
            }
            2 => {
                v___x_1000_ = l_Lean_Elab_instReprDocElabKind_repr___closed__3;
                crate::leanh::lean_inc(v___y_999_);
                v___x_1001_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1001_, 0, v___y_999_);
                crate::leanh::lean_ctor_set(v___x_1001_, 1, v___x_1000_);
                v___x_1002_ = 0;
                v___x_1003_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1003_, 0, v___x_1001_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1003_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1002_,
                );
                v___x_1004_ = l_Repr_addAppParen(v___x_1003_, v_prec_990_);
                return v___x_1004_;
            }
            3 => {
                v___x_1007_ = l_Lean_Elab_instReprDocElabKind_repr___closed__5;
                crate::leanh::lean_inc(v___y_1006_);
                v___x_1008_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1008_, 0, v___y_1006_);
                crate::leanh::lean_ctor_set(v___x_1008_, 1, v___x_1007_);
                v___x_1009_ = 0;
                v___x_1010_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1010_, 0, v___x_1008_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1010_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1009_,
                );
                v___x_1011_ = l_Repr_addAppParen(v___x_1010_, v_prec_990_);
                return v___x_1011_;
            }
            4 => {
                v___x_1014_ = l_Lean_Elab_instReprDocElabKind_repr___closed__7;
                crate::leanh::lean_inc(v___y_1013_);
                v___x_1015_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1015_, 0, v___y_1013_);
                crate::leanh::lean_ctor_set(v___x_1015_, 1, v___x_1014_);
                v___x_1016_ = 0;
                v___x_1017_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1017_, 0, v___x_1015_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1017_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1016_,
                );
                v___x_1018_ = l_Repr_addAppParen(v___x_1017_, v_prec_990_);
                return v___x_1018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instReprDocElabKind_repr___boxed(
    mut v_x_1035_: *mut crate::leanh::LeanObject,
    mut v_prec_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_233__boxed_1037_: u8 = 0;
    let mut v_res_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_233__boxed_1037_ = (crate::leanh::lean_unbox(v_x_1035_) as u8);
    v_res_1038_ = l_Lean_Elab_instReprDocElabKind_repr(v_x_233__boxed_1037_, v_prec_1036_);
    crate::leanh::lean_dec(v_prec_1036_);
    return v_res_1038_;
}
pub unsafe fn l_Lean_Elab_Info_ctorIdx(
    mut v_x_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1041_) {
        0 => {
            let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1042_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1042_;
        }
        1 => {
            let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1043_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1043_;
        }
        2 => {
            let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1044_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1044_;
        }
        3 => {
            let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1045_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1045_;
        }
        4 => {
            let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1046_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1046_;
        }
        5 => {
            let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1047_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_1047_;
        }
        6 => {
            let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1048_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_1048_;
        }
        7 => {
            let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1049_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_1049_;
        }
        8 => {
            let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1050_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_1050_;
        }
        9 => {
            let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1051_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_1051_;
        }
        10 => {
            let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1052_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_1052_;
        }
        11 => {
            let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1053_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_1053_;
        }
        12 => {
            let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1054_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_1054_;
        }
        13 => {
            let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1055_ = crate::leanh::lean_unsigned_to_nat(13);
            return v___x_1055_;
        }
        14 => {
            let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1056_ = crate::leanh::lean_unsigned_to_nat(14);
            return v___x_1056_;
        }
        15 => {
            let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1057_ = crate::leanh::lean_unsigned_to_nat(15);
            return v___x_1057_;
        }
        _ => {
            let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1058_ = crate::leanh::lean_unsigned_to_nat(16);
            return v___x_1058_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_ctorIdx___boxed(
    mut v_x_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lean_Elab_Info_ctorIdx(v_x_1059_);
    crate::leanh::lean_dec_ref(v_x_1059_);
    return v_res_1060_;
}
pub unsafe fn l_Lean_Elab_Info_ctorElim___redArg(
    mut v_t_1061_: *mut crate::leanh::LeanObject,
    mut v_k_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1061_) == 12 {
        let mut v_i_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_i_1063_ = crate::leanh::lean_ctor_get(v_t_1061_, 0);
        crate::leanh::lean_inc(v_i_1063_);
        crate::leanh::lean_dec_ref_known(v_t_1061_, 1);
        v___x_1064_ = crate::leanh::lean_apply_1(v_k_1062_, v_i_1063_);
        return v___x_1064_;
    } else {
        let mut v_i_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_i_1065_ = crate::leanh::lean_ctor_get(v_t_1061_, 0);
        crate::leanh::lean_inc_ref(v_i_1065_);
        crate::leanh::lean_dec_ref(v_t_1061_);
        v___x_1066_ = crate::leanh::lean_apply_1(v_k_1062_, v_i_1065_);
        return v___x_1066_;
    }
}
pub unsafe fn l_Lean_Elab_Info_ctorElim(
    mut v_motive_1067_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1068_: *mut crate::leanh::LeanObject,
    mut v_t_1069_: *mut crate::leanh::LeanObject,
    mut v_h_1070_: *mut crate::leanh::LeanObject,
    mut v_k_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1069_, v_k_1071_);
    return v___x_1072_;
}
pub unsafe fn l_Lean_Elab_Info_ctorElim___boxed(
    mut v_motive_1073_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1074_: *mut crate::leanh::LeanObject,
    mut v_t_1075_: *mut crate::leanh::LeanObject,
    mut v_h_1076_: *mut crate::leanh::LeanObject,
    mut v_k_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Lean_Elab_Info_ctorElim(
        v_motive_1073_,
        v_ctorIdx_1074_,
        v_t_1075_,
        v_h_1076_,
        v_k_1077_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1074_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_Elab_Info_ofTacticInfo_elim___redArg(
    mut v_t_1079_: *mut crate::leanh::LeanObject,
    mut v_ofTacticInfo_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1079_, v_ofTacticInfo_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_Elab_Info_ofTacticInfo_elim(
    mut v_motive_1082_: *mut crate::leanh::LeanObject,
    mut v_t_1083_: *mut crate::leanh::LeanObject,
    mut v_h_1084_: *mut crate::leanh::LeanObject,
    mut v_ofTacticInfo_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1083_, v_ofTacticInfo_1085_);
    return v___x_1086_;
}
pub unsafe fn l_Lean_Elab_Info_ofTermInfo_elim___redArg(
    mut v_t_1087_: *mut crate::leanh::LeanObject,
    mut v_ofTermInfo_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1087_, v_ofTermInfo_1088_);
    return v___x_1089_;
}
pub unsafe fn l_Lean_Elab_Info_ofTermInfo_elim(
    mut v_motive_1090_: *mut crate::leanh::LeanObject,
    mut v_t_1091_: *mut crate::leanh::LeanObject,
    mut v_h_1092_: *mut crate::leanh::LeanObject,
    mut v_ofTermInfo_1093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1091_, v_ofTermInfo_1093_);
    return v___x_1094_;
}
pub unsafe fn l_Lean_Elab_Info_ofPartialTermInfo_elim___redArg(
    mut v_t_1095_: *mut crate::leanh::LeanObject,
    mut v_ofPartialTermInfo_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1095_, v_ofPartialTermInfo_1096_);
    return v___x_1097_;
}
pub unsafe fn l_Lean_Elab_Info_ofPartialTermInfo_elim(
    mut v_motive_1098_: *mut crate::leanh::LeanObject,
    mut v_t_1099_: *mut crate::leanh::LeanObject,
    mut v_h_1100_: *mut crate::leanh::LeanObject,
    mut v_ofPartialTermInfo_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1099_, v_ofPartialTermInfo_1101_);
    return v___x_1102_;
}
pub unsafe fn l_Lean_Elab_Info_ofCommandInfo_elim___redArg(
    mut v_t_1103_: *mut crate::leanh::LeanObject,
    mut v_ofCommandInfo_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1103_, v_ofCommandInfo_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Elab_Info_ofCommandInfo_elim(
    mut v_motive_1106_: *mut crate::leanh::LeanObject,
    mut v_t_1107_: *mut crate::leanh::LeanObject,
    mut v_h_1108_: *mut crate::leanh::LeanObject,
    mut v_ofCommandInfo_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1107_, v_ofCommandInfo_1109_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_Elab_Info_ofMacroExpansionInfo_elim___redArg(
    mut v_t_1111_: *mut crate::leanh::LeanObject,
    mut v_ofMacroExpansionInfo_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1111_, v_ofMacroExpansionInfo_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Lean_Elab_Info_ofMacroExpansionInfo_elim(
    mut v_motive_1114_: *mut crate::leanh::LeanObject,
    mut v_t_1115_: *mut crate::leanh::LeanObject,
    mut v_h_1116_: *mut crate::leanh::LeanObject,
    mut v_ofMacroExpansionInfo_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1118_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1115_, v_ofMacroExpansionInfo_1117_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Elab_Info_ofOptionInfo_elim___redArg(
    mut v_t_1119_: *mut crate::leanh::LeanObject,
    mut v_ofOptionInfo_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1119_, v_ofOptionInfo_1120_);
    return v___x_1121_;
}
pub unsafe fn l_Lean_Elab_Info_ofOptionInfo_elim(
    mut v_motive_1122_: *mut crate::leanh::LeanObject,
    mut v_t_1123_: *mut crate::leanh::LeanObject,
    mut v_h_1124_: *mut crate::leanh::LeanObject,
    mut v_ofOptionInfo_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1123_, v_ofOptionInfo_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_Elab_Info_ofErrorNameInfo_elim___redArg(
    mut v_t_1127_: *mut crate::leanh::LeanObject,
    mut v_ofErrorNameInfo_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1127_, v_ofErrorNameInfo_1128_);
    return v___x_1129_;
}
pub unsafe fn l_Lean_Elab_Info_ofErrorNameInfo_elim(
    mut v_motive_1130_: *mut crate::leanh::LeanObject,
    mut v_t_1131_: *mut crate::leanh::LeanObject,
    mut v_h_1132_: *mut crate::leanh::LeanObject,
    mut v_ofErrorNameInfo_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1131_, v_ofErrorNameInfo_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldInfo_elim___redArg(
    mut v_t_1135_: *mut crate::leanh::LeanObject,
    mut v_ofFieldInfo_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1135_, v_ofFieldInfo_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldInfo_elim(
    mut v_motive_1138_: *mut crate::leanh::LeanObject,
    mut v_t_1139_: *mut crate::leanh::LeanObject,
    mut v_h_1140_: *mut crate::leanh::LeanObject,
    mut v_ofFieldInfo_1141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1139_, v_ofFieldInfo_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Lean_Elab_Info_ofCompletionInfo_elim___redArg(
    mut v_t_1143_: *mut crate::leanh::LeanObject,
    mut v_ofCompletionInfo_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1143_, v_ofCompletionInfo_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Lean_Elab_Info_ofCompletionInfo_elim(
    mut v_motive_1146_: *mut crate::leanh::LeanObject,
    mut v_t_1147_: *mut crate::leanh::LeanObject,
    mut v_h_1148_: *mut crate::leanh::LeanObject,
    mut v_ofCompletionInfo_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1147_, v_ofCompletionInfo_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lean_Elab_Info_ofUserWidgetInfo_elim___redArg(
    mut v_t_1151_: *mut crate::leanh::LeanObject,
    mut v_ofUserWidgetInfo_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1151_, v_ofUserWidgetInfo_1152_);
    return v___x_1153_;
}
pub unsafe fn l_Lean_Elab_Info_ofUserWidgetInfo_elim(
    mut v_motive_1154_: *mut crate::leanh::LeanObject,
    mut v_t_1155_: *mut crate::leanh::LeanObject,
    mut v_h_1156_: *mut crate::leanh::LeanObject,
    mut v_ofUserWidgetInfo_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1155_, v_ofUserWidgetInfo_1157_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_Elab_Info_ofCustomInfo_elim___redArg(
    mut v_t_1159_: *mut crate::leanh::LeanObject,
    mut v_ofCustomInfo_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1159_, v_ofCustomInfo_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Elab_Info_ofCustomInfo_elim(
    mut v_motive_1162_: *mut crate::leanh::LeanObject,
    mut v_t_1163_: *mut crate::leanh::LeanObject,
    mut v_h_1164_: *mut crate::leanh::LeanObject,
    mut v_ofCustomInfo_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1166_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1163_, v_ofCustomInfo_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Elab_Info_ofFVarAliasInfo_elim___redArg(
    mut v_t_1167_: *mut crate::leanh::LeanObject,
    mut v_ofFVarAliasInfo_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1167_, v_ofFVarAliasInfo_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Elab_Info_ofFVarAliasInfo_elim(
    mut v_motive_1170_: *mut crate::leanh::LeanObject,
    mut v_t_1171_: *mut crate::leanh::LeanObject,
    mut v_h_1172_: *mut crate::leanh::LeanObject,
    mut v_ofFVarAliasInfo_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1171_, v_ofFVarAliasInfo_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldRedeclInfo_elim___redArg(
    mut v_t_1175_: *mut crate::leanh::LeanObject,
    mut v_ofFieldRedeclInfo_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1175_, v_ofFieldRedeclInfo_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldRedeclInfo_elim(
    mut v_motive_1178_: *mut crate::leanh::LeanObject,
    mut v_t_1179_: *mut crate::leanh::LeanObject,
    mut v_h_1180_: *mut crate::leanh::LeanObject,
    mut v_ofFieldRedeclInfo_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1179_, v_ofFieldRedeclInfo_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Lean_Elab_Info_ofDelabTermInfo_elim___redArg(
    mut v_t_1183_: *mut crate::leanh::LeanObject,
    mut v_ofDelabTermInfo_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1183_, v_ofDelabTermInfo_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Lean_Elab_Info_ofDelabTermInfo_elim(
    mut v_motive_1186_: *mut crate::leanh::LeanObject,
    mut v_t_1187_: *mut crate::leanh::LeanObject,
    mut v_h_1188_: *mut crate::leanh::LeanObject,
    mut v_ofDelabTermInfo_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1187_, v_ofDelabTermInfo_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Lean_Elab_Info_ofChoiceInfo_elim___redArg(
    mut v_t_1191_: *mut crate::leanh::LeanObject,
    mut v_ofChoiceInfo_1192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1191_, v_ofChoiceInfo_1192_);
    return v___x_1193_;
}
pub unsafe fn l_Lean_Elab_Info_ofChoiceInfo_elim(
    mut v_motive_1194_: *mut crate::leanh::LeanObject,
    mut v_t_1195_: *mut crate::leanh::LeanObject,
    mut v_h_1196_: *mut crate::leanh::LeanObject,
    mut v_ofChoiceInfo_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1195_, v_ofChoiceInfo_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocInfo_elim___redArg(
    mut v_t_1199_: *mut crate::leanh::LeanObject,
    mut v_ofDocInfo_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1199_, v_ofDocInfo_1200_);
    return v___x_1201_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocInfo_elim(
    mut v_motive_1202_: *mut crate::leanh::LeanObject,
    mut v_t_1203_: *mut crate::leanh::LeanObject,
    mut v_h_1204_: *mut crate::leanh::LeanObject,
    mut v_ofDocInfo_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1203_, v_ofDocInfo_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocElabInfo_elim___redArg(
    mut v_t_1207_: *mut crate::leanh::LeanObject,
    mut v_ofDocElabInfo_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1209_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1207_, v_ofDocElabInfo_1208_);
    return v___x_1209_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocElabInfo_elim(
    mut v_motive_1210_: *mut crate::leanh::LeanObject,
    mut v_t_1211_: *mut crate::leanh::LeanObject,
    mut v_h_1212_: *mut crate::leanh::LeanObject,
    mut v_ofDocElabInfo_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1211_, v_ofDocElabInfo_1213_);
    return v___x_1214_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfo_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = l_Lean_Elab_instInhabitedTacticInfo_default;
    v___x_1216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1216_, 0, v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfo_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedInfo_default___closed__0,
    );
    return v___x_1217_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ = l_Lean_Elab_instInhabitedInfo_default;
    return v___x_1218_;
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorIdx(
    mut v_x_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1219_) {
        0 => {
            let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1220_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1220_;
        }
        1 => {
            let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1221_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1221_;
        }
        _ => {
            let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1222_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1222_;
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorIdx___boxed(
    mut v_x_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Elab_InfoTree_ctorIdx(v_x_1223_);
    crate::leanh::lean_dec_ref(v_x_1223_);
    return v_res_1224_;
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorElim___redArg(
    mut v_t_1225_: *mut crate::leanh::LeanObject,
    mut v_k_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1225_) == 2 {
        let mut v_mvarId_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_1227_ = crate::leanh::lean_ctor_get(v_t_1225_, 0);
        crate::leanh::lean_inc(v_mvarId_1227_);
        crate::leanh::lean_dec_ref_known(v_t_1225_, 1);
        v___x_1228_ = crate::leanh::lean_apply_1(v_k_1226_, v_mvarId_1227_);
        return v___x_1228_;
    } else {
        let mut v_i_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_t_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_i_1229_ = crate::leanh::lean_ctor_get(v_t_1225_, 0);
        crate::leanh::lean_inc_ref(v_i_1229_);
        v_t_1230_ = crate::leanh::lean_ctor_get(v_t_1225_, 1);
        crate::leanh::lean_inc_ref(v_t_1230_);
        crate::leanh::lean_dec_ref(v_t_1225_);
        v___x_1231_ = crate::leanh::lean_apply_2(v_k_1226_, v_i_1229_, v_t_1230_);
        return v___x_1231_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorElim(
    mut v_motive__1_1232_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1233_: *mut crate::leanh::LeanObject,
    mut v_t_1234_: *mut crate::leanh::LeanObject,
    mut v_h_1235_: *mut crate::leanh::LeanObject,
    mut v_k_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1234_, v_k_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorElim___boxed(
    mut v_motive__1_1238_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1239_: *mut crate::leanh::LeanObject,
    mut v_t_1240_: *mut crate::leanh::LeanObject,
    mut v_h_1241_: *mut crate::leanh::LeanObject,
    mut v_k_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Lean_Elab_InfoTree_ctorElim(
        v_motive__1_1238_,
        v_ctorIdx_1239_,
        v_t_1240_,
        v_h_1241_,
        v_k_1242_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1239_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_Elab_InfoTree_context_elim___redArg(
    mut v_t_1244_: *mut crate::leanh::LeanObject,
    mut v_context_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1244_, v_context_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Lean_Elab_InfoTree_context_elim(
    mut v_motive__1_1247_: *mut crate::leanh::LeanObject,
    mut v_t_1248_: *mut crate::leanh::LeanObject,
    mut v_h_1249_: *mut crate::leanh::LeanObject,
    mut v_context_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1248_, v_context_1250_);
    return v___x_1251_;
}
pub unsafe fn l_Lean_Elab_InfoTree_node_elim___redArg(
    mut v_t_1252_: *mut crate::leanh::LeanObject,
    mut v_node_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1252_, v_node_1253_);
    return v___x_1254_;
}
pub unsafe fn l_Lean_Elab_InfoTree_node_elim(
    mut v_motive__1_1255_: *mut crate::leanh::LeanObject,
    mut v_t_1256_: *mut crate::leanh::LeanObject,
    mut v_h_1257_: *mut crate::leanh::LeanObject,
    mut v_node_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1259_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1256_, v_node_1258_);
    return v___x_1259_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hole_elim___redArg(
    mut v_t_1260_: *mut crate::leanh::LeanObject,
    mut v_hole_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1260_, v_hole_1261_);
    return v___x_1262_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hole_elim(
    mut v_motive__1_1263_: *mut crate::leanh::LeanObject,
    mut v_t_1264_: *mut crate::leanh::LeanObject,
    mut v_h_1265_: *mut crate::leanh::LeanObject,
    mut v_hole_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1264_, v_hole_1266_);
    return v___x_1267_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ = l_Lean_instInhabitedPersistentArray_default(crate::leanh::lean_box(0));
    return v___x_1268_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0,
    );
    v___x_1270_ = l_Lean_Elab_instInhabitedInfo_default;
    v___x_1271_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
    crate::leanh::lean_ctor_set(v___x_1271_, 1, v___x_1269_);
    return v___x_1271_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once),
        _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1,
    );
    return v___x_1272_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree() -> *mut crate::leanh::LeanObject {
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lean_Elab_instInhabitedInfoTree_default;
    return v___x_1273_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1274_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0,
    );
    v___x_1276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1276_, 0, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1278_ = lean_mk_empty_array_with_capacity(v___x_1277_);
    v___x_1279_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1279_, 0, v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1280_: usize = 0;
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = 5usize;
    v___x_1281_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1282_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1283_ = lean_mk_empty_array_with_capacity(v___x_1282_);
    v___x_1284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2,
    );
    v___x_1285_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1285_, 0, v___x_1284_);
    crate::leanh::lean_ctor_set(v___x_1285_, 1, v___x_1283_);
    crate::leanh::lean_ctor_set(v___x_1285_, 2, v___x_1281_);
    crate::leanh::lean_ctor_set(v___x_1285_, 3, v___x_1281_);
    crate::leanh::lean_ctor_set_usize(v___x_1285_, 4, v___x_1280_);
    return v___x_1285_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__3_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3,
    );
    v___x_1287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__1_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1,
    );
    v___x_1288_ = 1;
    v___x_1289_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1287_);
    crate::leanh::lean_ctor_set(v___x_1289_, 1, v___x_1287_);
    crate::leanh::lean_ctor_set(v___x_1289_, 2, v___x_1286_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1289_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1288_,
    );
    return v___x_1289_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__4_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__4,
    );
    return v___x_1290_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState() -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Elab_instInhabitedInfoState_default;
    return v___x_1291_;
}
pub unsafe fn l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(
    mut v_modifyInfoState_1292_: *mut crate::leanh::LeanObject,
    mut v_inst_1293_: *mut crate::leanh::LeanObject,
    mut v_f_1294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ = crate::leanh::lean_apply_1(v_modifyInfoState_1292_, v_f_1294_);
    v___x_1296_ = crate::leanh::lean_apply_2(v_inst_1293_, crate::leanh::lean_box(0), v___x_1295_);
    return v___x_1296_;
}
pub unsafe fn l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(
    mut v_inst_1297_: *mut crate::leanh::LeanObject,
    mut v_inst_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getInfoState_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___f_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getInfoState_1299_ = crate::leanh::lean_ctor_get(v_inst_1298_, 0);
                v_modifyInfoState_1300_ = crate::leanh::lean_ctor_get(v_inst_1298_, 1);
                v_isSharedCheck_1309_ = (!crate::leanh::lean_is_exclusive(v_inst_1298_)) as u8;
                if v_isSharedCheck_1309_ == 0 {
                    v___x_1302_ = v_inst_1298_;
                    v_isShared_1303_ = v_isSharedCheck_1309_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_modifyInfoState_1300_);
                    crate::leanh::lean_inc(v_getInfoState_1299_);
                    crate::leanh::lean_dec(v_inst_1298_);
                    v___x_1302_ = crate::leanh::lean_box(0);
                    v_isShared_1303_ = v_isSharedCheck_1309_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_inst_1297_);
                v___f_1304_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1304_, 0, v_modifyInfoState_1300_);
                crate::leanh::lean_closure_set(v___f_1304_, 1, v_inst_1297_);
                v___x_1305_ = crate::leanh::lean_apply_2(
                    v_inst_1297_,
                    crate::leanh::lean_box(0),
                    v_getInfoState_1299_,
                );
                if v_isShared_1303_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1302_, 1, v___f_1304_);
                    crate::leanh::lean_ctor_set(v___x_1302_, 0, v___x_1305_);
                    v___x_1307_ = v___x_1302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___f_1304_);
                    v___x_1307_ = v_reuseFailAlloc_1308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_instMonadInfoTreeOfMonadLift(
    mut v_m_1310_: *mut crate::leanh::LeanObject,
    mut v_n_1311_: *mut crate::leanh::LeanObject,
    mut v_inst_1312_: *mut crate::leanh::LeanObject,
    mut v_inst_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v_inst_1312_, v_inst_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Lean_Elab_setInfoState___redArg___lam__0(
    mut v_s_1315_: *mut crate::leanh::LeanObject,
    mut v_x_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_1315_);
    return v_s_1315_;
}
pub unsafe fn l_Lean_Elab_setInfoState___redArg___lam__0___boxed(
    mut v_s_1317_: *mut crate::leanh::LeanObject,
    mut v_x_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Lean_Elab_setInfoState___redArg___lam__0(v_s_1317_, v_x_1318_);
    crate::leanh::lean_dec_ref(v_x_1318_);
    crate::leanh::lean_dec_ref(v_s_1317_);
    return v_res_1319_;
}
pub unsafe fn l_Lean_Elab_setInfoState___redArg(
    mut v_inst_1320_: *mut crate::leanh::LeanObject,
    mut v_s_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modifyInfoState_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modifyInfoState_1322_ = crate::leanh::lean_ctor_get(v_inst_1320_, 1);
    crate::leanh::lean_inc(v_modifyInfoState_1322_);
    crate::leanh::lean_dec_ref(v_inst_1320_);
    v___f_1323_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_setInfoState___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1323_, 0, v_s_1321_);
    v___x_1324_ = crate::leanh::lean_apply_1(v_modifyInfoState_1322_, v___f_1323_);
    return v___x_1324_;
}
pub unsafe fn l_Lean_Elab_setInfoState(
    mut v_m_1325_: *mut crate::leanh::LeanObject,
    mut v_inst_1326_: *mut crate::leanh::LeanObject,
    mut v_s_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1328_ = l_Lean_Elab_setInfoState___redArg(v_inst_1326_, v_s_1327_);
    return v___x_1328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_InfoTree_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_OpenDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PPContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_MetavarContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedTermInfo_default = _init_l_Lean_Elab_instInhabitedTermInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo_default);
    l_Lean_Elab_instInhabitedTermInfo = _init_l_Lean_Elab_instInhabitedTermInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo);
    l_Lean_Elab_instInhabitedPartialTermInfo_default =
        _init_l_Lean_Elab_instInhabitedPartialTermInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo_default);
    l_Lean_Elab_instInhabitedPartialTermInfo = _init_l_Lean_Elab_instInhabitedPartialTermInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo);
    l_Lean_Elab_instInhabitedFieldInfo_default = _init_l_Lean_Elab_instInhabitedFieldInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo_default);
    l_Lean_Elab_instInhabitedFieldInfo = _init_l_Lean_Elab_instInhabitedFieldInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo);
    l_Lean_Elab_instInhabitedTacticInfo_default =
        _init_l_Lean_Elab_instInhabitedTacticInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo_default);
    l_Lean_Elab_instInhabitedTacticInfo = _init_l_Lean_Elab_instInhabitedTacticInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo);
    l_Lean_Elab_instInhabitedMacroExpansionInfo_default =
        _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo_default);
    l_Lean_Elab_instInhabitedMacroExpansionInfo =
        _init_l_Lean_Elab_instInhabitedMacroExpansionInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo);
    l_Lean_Elab_instInhabitedInfo_default = _init_l_Lean_Elab_instInhabitedInfo_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfo_default);
    l_Lean_Elab_instInhabitedInfo = _init_l_Lean_Elab_instInhabitedInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfo);
    l_Lean_Elab_instInhabitedInfoTree_default = _init_l_Lean_Elab_instInhabitedInfoTree_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree_default);
    l_Lean_Elab_instInhabitedInfoTree = _init_l_Lean_Elab_instInhabitedInfoTree();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree);
    l_Lean_Elab_instInhabitedInfoState_default = _init_l_Lean_Elab_instInhabitedInfoState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState_default);
    l_Lean_Elab_instInhabitedInfoState = _init_l_Lean_Elab_instInhabitedInfoState();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_InfoTree_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_InfoTree_Types(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_OpenDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PPContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_MetavarContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Environment(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Widget_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_InfoTree_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_InfoTree_Types(builtin);
}
