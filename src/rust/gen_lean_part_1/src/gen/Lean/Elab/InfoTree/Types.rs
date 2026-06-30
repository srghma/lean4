// Lean compiler output
// Module: Lean.Elab.InfoTree.Types
// Imports: Lean.Data.DeclarationRange Lean.Data.OpenDecl Lean.Data.PPContext Lean.MetavarContext Lean.Environment Lean.Widget.Types
use crate::ffi::{lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_to_int};
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
pub static l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedElabInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedElabInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedElabInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
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
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTermInfo_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_instInhabitedTermInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTermInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedTermInfo_default___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTermInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTermInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedPartialTermInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedPartialTermInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedCommandInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedCommandInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedElabInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedFieldInfo_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedFieldInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedFieldInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedFieldInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedTacticInfo_default___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTacticInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedTacticInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedMacroExpansionInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedMacroExpansionInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__0_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__2_value: leanh::LeanStringObject<
    32,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__4_value: leanh::LeanStringObject<
    32,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__6_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instReprDocElabKind_repr___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind_repr___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instReprDocElabKind_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_instReprDocElabKind___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_instReprDocElabKind_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_instReprDocElabKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instReprDocElabKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instReprDocElabKind___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_instInhabitedInfo_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfo: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoTree_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoTree_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoTree: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_instInhabitedInfoState_default___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoState_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_instInhabitedInfoState: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorIdx(
    mut v_x_665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_665_) {
        0 => {
            let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_666_ = leanh::lean_unsigned_to_nat(0);
            return v___x_666_;
        }
        1 => {
            let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_667_ = leanh::lean_unsigned_to_nat(1);
            return v___x_667_;
        }
        _ => {
            let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_668_ = leanh::lean_unsigned_to_nat(2);
            return v___x_668_;
        }
    }
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorIdx___boxed(
    mut v_x_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Lean_Elab_PartialContextInfo_ctorIdx(v_x_669_);
    leanh::lean_dec_ref(v_x_669_);
    return v_res_670_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorElim___redArg(
    mut v_t_671_: *mut leanh::LeanObject,
    mut v_k_672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_671_) == 1 {
        let mut v_parentDecl_673_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_parentDecl_673_ = leanh::lean_ctor_get(v_t_671_, 0);
        leanh::lean_inc(v_parentDecl_673_);
        leanh::lean_dec_ref_known(v_t_671_, 1);
        v___x_674_ = leanh::lean_apply_1(v_k_672_, v_parentDecl_673_);
        return v___x_674_;
    } else {
        let mut v_info_675_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_info_675_ = leanh::lean_ctor_get(v_t_671_, 0);
        leanh::lean_inc_ref(v_info_675_);
        leanh::lean_dec_ref(v_t_671_);
        v___x_676_ = leanh::lean_apply_1(v_k_672_, v_info_675_);
        return v___x_676_;
    }
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorElim(
    mut v_motive_677_: *mut leanh::LeanObject,
    mut v_ctorIdx_678_: *mut leanh::LeanObject,
    mut v_t_679_: *mut leanh::LeanObject,
    mut v_h_680_: *mut leanh::LeanObject,
    mut v_k_681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_679_, v_k_681_);
    return v___x_682_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_ctorElim___boxed(
    mut v_motive_683_: *mut leanh::LeanObject,
    mut v_ctorIdx_684_: *mut leanh::LeanObject,
    mut v_t_685_: *mut leanh::LeanObject,
    mut v_h_686_: *mut leanh::LeanObject,
    mut v_k_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_Elab_PartialContextInfo_ctorElim(
        v_motive_683_,
        v_ctorIdx_684_,
        v_t_685_,
        v_h_686_,
        v_k_687_,
    );
    leanh::lean_dec(v_ctorIdx_684_);
    return v_res_688_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_commandCtx_elim___redArg(
    mut v_t_689_: *mut leanh::LeanObject,
    mut v_commandCtx_690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_689_, v_commandCtx_690_);
    return v___x_691_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_commandCtx_elim(
    mut v_motive_692_: *mut leanh::LeanObject,
    mut v_t_693_: *mut leanh::LeanObject,
    mut v_h_694_: *mut leanh::LeanObject,
    mut v_commandCtx_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_693_, v_commandCtx_695_);
    return v___x_696_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim___redArg(
    mut v_t_697_: *mut leanh::LeanObject,
    mut v_parentDeclCtx_698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_697_, v_parentDeclCtx_698_);
    return v___x_699_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_parentDeclCtx_elim(
    mut v_motive_700_: *mut leanh::LeanObject,
    mut v_t_701_: *mut leanh::LeanObject,
    mut v_h_702_: *mut leanh::LeanObject,
    mut v_parentDeclCtx_703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_701_, v_parentDeclCtx_703_);
    return v___x_704_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim___redArg(
    mut v_t_705_: *mut leanh::LeanObject,
    mut v_autoImplicitCtx_706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_707_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_705_, v_autoImplicitCtx_706_);
    return v___x_707_;
}
pub unsafe fn l_Lean_Elab_PartialContextInfo_autoImplicitCtx_elim(
    mut v_motive_708_: *mut leanh::LeanObject,
    mut v_t_709_: *mut leanh::LeanObject,
    mut v_h_710_: *mut leanh::LeanObject,
    mut v_autoImplicitCtx_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_Lean_Elab_PartialContextInfo_ctorElim___redArg(v_t_709_, v_autoImplicitCtx_711_);
    return v___x_712_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = leanh::lean_box(0);
    v___x_722_ = l_Lean_Elab_instInhabitedTermInfo_default___closed__1;
    v___x_723_ = l_Lean_Expr_const___override(v___x_722_, v___x_721_);
    return v___x_723_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = 0;
    v___x_725_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2,
    );
    v___x_726_ = leanh::lean_box(0);
    v___x_727_ = l_Lean_instInhabitedLocalContext_default;
    v___x_728_ = l_Lean_Elab_instInhabitedElabInfo_default;
    v___x_729_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
    leanh::lean_ctor_set(v___x_729_, 0, v___x_728_);
    leanh::lean_ctor_set(v___x_729_, 1, v___x_727_);
    leanh::lean_ctor_set(v___x_729_, 2, v___x_726_);
    leanh::lean_ctor_set(v___x_729_, 3, v___x_725_);
    leanh::lean_ctor_set_uint8(
        v___x_729_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_724_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_729_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
        v___x_724_,
    );
    return v___x_729_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo_default() -> *mut leanh::LeanObject {
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_730_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__3_once),
        _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__3,
    );
    return v___x_730_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTermInfo() -> *mut leanh::LeanObject {
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lean_Elab_instInhabitedTermInfo_default;
    return v___x_731_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = leanh::lean_box(0);
    v___x_733_ = l_Lean_instInhabitedLocalContext_default;
    v___x_734_ = l_Lean_Elab_instInhabitedElabInfo_default;
    v___x_735_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_735_, 0, v___x_734_);
    leanh::lean_ctor_set(v___x_735_, 1, v___x_733_);
    leanh::lean_ctor_set(v___x_735_, 2, v___x_732_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialTermInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedPartialTermInfo_default___closed__0,
    );
    return v___x_736_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialTermInfo() -> *mut leanh::LeanObject {
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_Elab_instInhabitedPartialTermInfo_default;
    return v___x_737_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorIdx(
    mut v_x_740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_740_) {
        0 => {
            let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_741_ = leanh::lean_unsigned_to_nat(0);
            return v___x_741_;
        }
        1 => {
            let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_742_ = leanh::lean_unsigned_to_nat(1);
            return v___x_742_;
        }
        2 => {
            let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_743_ = leanh::lean_unsigned_to_nat(2);
            return v___x_743_;
        }
        3 => {
            let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_744_ = leanh::lean_unsigned_to_nat(3);
            return v___x_744_;
        }
        4 => {
            let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_745_ = leanh::lean_unsigned_to_nat(4);
            return v___x_745_;
        }
        5 => {
            let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_746_ = leanh::lean_unsigned_to_nat(5);
            return v___x_746_;
        }
        6 => {
            let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_747_ = leanh::lean_unsigned_to_nat(6);
            return v___x_747_;
        }
        7 => {
            let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_748_ = leanh::lean_unsigned_to_nat(7);
            return v___x_748_;
        }
        _ => {
            let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_749_ = leanh::lean_unsigned_to_nat(8);
            return v___x_749_;
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorIdx___boxed(
    mut v_x_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Lean_Elab_CompletionInfo_ctorIdx(v_x_750_);
    leanh::lean_dec_ref(v_x_750_);
    return v_res_751_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorElim___redArg(
    mut v_t_752_: *mut leanh::LeanObject,
    mut v_k_753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_752_) {
        0 => {
            let mut v_termInfo_754_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedType_x3f_755_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_termInfo_754_ = leanh::lean_ctor_get(v_t_752_, 0);
            leanh::lean_inc_ref(v_termInfo_754_);
            v_expectedType_x3f_755_ = leanh::lean_ctor_get(v_t_752_, 1);
            leanh::lean_inc(v_expectedType_x3f_755_);
            leanh::lean_dec_ref_known(v_t_752_, 2);
            v___x_756_ =
                leanh::lean_apply_2(v_k_753_, v_termInfo_754_, v_expectedType_x3f_755_);
            return v___x_756_;
        }
        1 => {
            let mut v_stx_757_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_758_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_danglingDot_759_: u8 = 0;
            let mut v_lctx_760_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedType_x3f_761_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_stx_757_ = leanh::lean_ctor_get(v_t_752_, 0);
            leanh::lean_inc(v_stx_757_);
            v_id_758_ = leanh::lean_ctor_get(v_t_752_, 1);
            leanh::lean_inc(v_id_758_);
            v_danglingDot_759_ = leanh::lean_ctor_get_uint8(
                v_t_752_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            v_lctx_760_ = leanh::lean_ctor_get(v_t_752_, 2);
            leanh::lean_inc_ref(v_lctx_760_);
            v_expectedType_x3f_761_ = leanh::lean_ctor_get(v_t_752_, 3);
            leanh::lean_inc(v_expectedType_x3f_761_);
            leanh::lean_dec_ref_known(v_t_752_, 4);
            v___x_762_ = leanh::lean_box((v_danglingDot_759_) as usize);
            v___x_763_ = leanh::lean_apply_5(
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
            let mut v_stx_764_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_765_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lctx_766_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedType_x3f_767_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_stx_764_ = leanh::lean_ctor_get(v_t_752_, 0);
            leanh::lean_inc(v_stx_764_);
            v_id_765_ = leanh::lean_ctor_get(v_t_752_, 1);
            leanh::lean_inc(v_id_765_);
            v_lctx_766_ = leanh::lean_ctor_get(v_t_752_, 2);
            leanh::lean_inc_ref(v_lctx_766_);
            v_expectedType_x3f_767_ = leanh::lean_ctor_get(v_t_752_, 3);
            leanh::lean_inc(v_expectedType_x3f_767_);
            leanh::lean_dec_ref_known(v_t_752_, 4);
            v___x_768_ = leanh::lean_apply_4(
                v_k_753_,
                v_stx_764_,
                v_id_765_,
                v_lctx_766_,
                v_expectedType_x3f_767_,
            );
            return v___x_768_;
        }
        3 => {
            let mut v_stx_769_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_770_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lctx_771_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_structName_772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_stx_769_ = leanh::lean_ctor_get(v_t_752_, 0);
            leanh::lean_inc(v_stx_769_);
            v_id_770_ = leanh::lean_ctor_get(v_t_752_, 1);
            leanh::lean_inc(v_id_770_);
            v_lctx_771_ = leanh::lean_ctor_get(v_t_752_, 2);
            leanh::lean_inc_ref(v_lctx_771_);
            v_structName_772_ = leanh::lean_ctor_get(v_t_752_, 3);
            leanh::lean_inc(v_structName_772_);
            leanh::lean_dec_ref_known(v_t_752_, 4);
            v___x_773_ = leanh::lean_apply_4(
                v_k_753_,
                v_stx_769_,
                v_id_770_,
                v_lctx_771_,
                v_structName_772_,
            );
            return v___x_773_;
        }
        6 => {
            let mut v_stx_774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_partialId_775_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_stx_774_ = leanh::lean_ctor_get(v_t_752_, 0);
            leanh::lean_inc(v_stx_774_);
            v_partialId_775_ = leanh::lean_ctor_get(v_t_752_, 1);
            leanh::lean_inc(v_partialId_775_);
            leanh::lean_dec_ref_known(v_t_752_, 2);
            v___x_776_ = leanh::lean_apply_2(v_k_753_, v_stx_774_, v_partialId_775_);
            return v___x_776_;
        }
        7 => {
            let mut v_stx_777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_x3f_778_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_danglingDot_779_: u8 = 0;
            let mut v_scopeNames_780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_stx_777_ = leanh::lean_ctor_get(v_t_752_, 0);
            leanh::lean_inc(v_stx_777_);
            v_id_x3f_778_ = leanh::lean_ctor_get(v_t_752_, 1);
            leanh::lean_inc(v_id_x3f_778_);
            v_danglingDot_779_ = leanh::lean_ctor_get_uint8(
                v_t_752_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            v_scopeNames_780_ = leanh::lean_ctor_get(v_t_752_, 2);
            leanh::lean_inc(v_scopeNames_780_);
            leanh::lean_dec_ref_known(v_t_752_, 3);
            v___x_781_ = leanh::lean_box((v_danglingDot_779_) as usize);
            v___x_782_ = leanh::lean_apply_4(
                v_k_753_,
                v_stx_777_,
                v_id_x3f_778_,
                v___x_781_,
                v_scopeNames_780_,
            );
            return v___x_782_;
        }
        _ => {
            let mut v_stx_783_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_stx_783_ = leanh::lean_ctor_get(v_t_752_, 0);
            leanh::lean_inc(v_stx_783_);
            leanh::lean_dec_ref(v_t_752_);
            v___x_784_ = leanh::lean_apply_1(v_k_753_, v_stx_783_);
            return v___x_784_;
        }
    }
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorElim(
    mut v_motive_785_: *mut leanh::LeanObject,
    mut v_ctorIdx_786_: *mut leanh::LeanObject,
    mut v_t_787_: *mut leanh::LeanObject,
    mut v_h_788_: *mut leanh::LeanObject,
    mut v_k_789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_787_, v_k_789_);
    return v___x_790_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_ctorElim___boxed(
    mut v_motive_791_: *mut leanh::LeanObject,
    mut v_ctorIdx_792_: *mut leanh::LeanObject,
    mut v_t_793_: *mut leanh::LeanObject,
    mut v_h_794_: *mut leanh::LeanObject,
    mut v_k_795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_796_ = l_Lean_Elab_CompletionInfo_ctorElim(
        v_motive_791_,
        v_ctorIdx_792_,
        v_t_793_,
        v_h_794_,
        v_k_795_,
    );
    leanh::lean_dec(v_ctorIdx_792_);
    return v_res_796_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dot_elim___redArg(
    mut v_t_797_: *mut leanh::LeanObject,
    mut v_dot_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_797_, v_dot_798_);
    return v___x_799_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dot_elim(
    mut v_motive_800_: *mut leanh::LeanObject,
    mut v_t_801_: *mut leanh::LeanObject,
    mut v_h_802_: *mut leanh::LeanObject,
    mut v_dot_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_801_, v_dot_803_);
    return v___x_804_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_id_elim___redArg(
    mut v_t_805_: *mut leanh::LeanObject,
    mut v_id_806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_805_, v_id_806_);
    return v___x_807_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_id_elim(
    mut v_motive_808_: *mut leanh::LeanObject,
    mut v_t_809_: *mut leanh::LeanObject,
    mut v_h_810_: *mut leanh::LeanObject,
    mut v_id_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_809_, v_id_811_);
    return v___x_812_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dotId_elim___redArg(
    mut v_t_813_: *mut leanh::LeanObject,
    mut v_dotId_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_813_, v_dotId_814_);
    return v___x_815_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_dotId_elim(
    mut v_motive_816_: *mut leanh::LeanObject,
    mut v_t_817_: *mut leanh::LeanObject,
    mut v_h_818_: *mut leanh::LeanObject,
    mut v_dotId_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_817_, v_dotId_819_);
    return v___x_820_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_fieldId_elim___redArg(
    mut v_t_821_: *mut leanh::LeanObject,
    mut v_fieldId_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_821_, v_fieldId_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_fieldId_elim(
    mut v_motive_824_: *mut leanh::LeanObject,
    mut v_t_825_: *mut leanh::LeanObject,
    mut v_h_826_: *mut leanh::LeanObject,
    mut v_fieldId_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_825_, v_fieldId_827_);
    return v___x_828_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_namespaceId_elim___redArg(
    mut v_t_829_: *mut leanh::LeanObject,
    mut v_namespaceId_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_829_, v_namespaceId_830_);
    return v___x_831_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_namespaceId_elim(
    mut v_motive_832_: *mut leanh::LeanObject,
    mut v_t_833_: *mut leanh::LeanObject,
    mut v_h_834_: *mut leanh::LeanObject,
    mut v_namespaceId_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_833_, v_namespaceId_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_option_elim___redArg(
    mut v_t_837_: *mut leanh::LeanObject,
    mut v_option_838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_837_, v_option_838_);
    return v___x_839_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_option_elim(
    mut v_motive_840_: *mut leanh::LeanObject,
    mut v_t_841_: *mut leanh::LeanObject,
    mut v_h_842_: *mut leanh::LeanObject,
    mut v_option_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_844_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_841_, v_option_843_);
    return v___x_844_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_errorName_elim___redArg(
    mut v_t_845_: *mut leanh::LeanObject,
    mut v_errorName_846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_847_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_845_, v_errorName_846_);
    return v___x_847_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_errorName_elim(
    mut v_motive_848_: *mut leanh::LeanObject,
    mut v_t_849_: *mut leanh::LeanObject,
    mut v_h_850_: *mut leanh::LeanObject,
    mut v_errorName_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_849_, v_errorName_851_);
    return v___x_852_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_endSection_elim___redArg(
    mut v_t_853_: *mut leanh::LeanObject,
    mut v_endSection_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_853_, v_endSection_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_endSection_elim(
    mut v_motive_856_: *mut leanh::LeanObject,
    mut v_t_857_: *mut leanh::LeanObject,
    mut v_h_858_: *mut leanh::LeanObject,
    mut v_endSection_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_857_, v_endSection_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_tactic_elim___redArg(
    mut v_t_861_: *mut leanh::LeanObject,
    mut v_tactic_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_861_, v_tactic_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_Elab_CompletionInfo_tactic_elim(
    mut v_motive_864_: *mut leanh::LeanObject,
    mut v_t_865_: *mut leanh::LeanObject,
    mut v_h_866_: *mut leanh::LeanObject,
    mut v_tactic_867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = l_Lean_Elab_CompletionInfo_ctorElim___redArg(v_t_865_, v_tactic_867_);
    return v___x_868_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = leanh::lean_box(0);
    v___x_870_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTermInfo_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedTermInfo_default___closed__2,
    );
    v___x_871_ = l_Lean_instInhabitedLocalContext_default;
    v___x_872_ = leanh::lean_box(0);
    v___x_873_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_873_, 0, v___x_872_);
    leanh::lean_ctor_set(v___x_873_, 1, v___x_872_);
    leanh::lean_ctor_set(v___x_873_, 2, v___x_871_);
    leanh::lean_ctor_set(v___x_873_, 3, v___x_870_);
    leanh::lean_ctor_set(v___x_873_, 4, v___x_869_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedFieldInfo_default() -> *mut leanh::LeanObject {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedFieldInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedFieldInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedFieldInfo_default___closed__0,
    );
    return v___x_874_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedFieldInfo() -> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_Lean_Elab_instInhabitedFieldInfo_default;
    return v___x_875_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__0,
    );
    v___x_878_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_878_, 0, v___x_877_);
    return v___x_878_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__1_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__1,
    );
    v___x_880_ = leanh::lean_unsigned_to_nat(0);
    v___x_881_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_881_, 0, v___x_880_);
    leanh::lean_ctor_set(v___x_881_, 1, v___x_880_);
    leanh::lean_ctor_set(v___x_881_, 2, v___x_880_);
    leanh::lean_ctor_set(v___x_881_, 3, v___x_880_);
    leanh::lean_ctor_set(v___x_881_, 4, v___x_879_);
    leanh::lean_ctor_set(v___x_881_, 5, v___x_879_);
    leanh::lean_ctor_set(v___x_881_, 6, v___x_879_);
    leanh::lean_ctor_set(v___x_881_, 7, v___x_879_);
    leanh::lean_ctor_set(v___x_881_, 8, v___x_879_);
    leanh::lean_ctor_set(v___x_881_, 9, v___x_879_);
    return v___x_881_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_882_ = leanh::lean_box(0);
    v___x_883_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__2,
    );
    v___x_884_ = l_Lean_Elab_instInhabitedElabInfo_default;
    v___x_885_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_885_, 0, v___x_884_);
    leanh::lean_ctor_set(v___x_885_, 1, v___x_883_);
    leanh::lean_ctor_set(v___x_885_, 2, v___x_882_);
    leanh::lean_ctor_set(v___x_885_, 3, v___x_883_);
    leanh::lean_ctor_set(v___x_885_, 4, v___x_882_);
    return v___x_885_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo_default() -> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedTacticInfo_default___closed__3_once),
        _init_l_Lean_Elab_instInhabitedTacticInfo_default___closed__3,
    );
    return v___x_886_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedTacticInfo() -> *mut leanh::LeanObject {
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = l_Lean_Elab_instInhabitedTacticInfo_default;
    return v___x_887_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = leanh::lean_box(0);
    v___x_889_ = l_Lean_instInhabitedLocalContext_default;
    v___x_890_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_890_, 0, v___x_889_);
    leanh::lean_ctor_set(v___x_890_, 1, v___x_888_);
    leanh::lean_ctor_set(v___x_890_, 2, v___x_888_);
    return v___x_890_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0_once
        ),
        _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default___closed__0,
    );
    return v___x_891_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedMacroExpansionInfo() -> *mut leanh::LeanObject {
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_892_ = l_Lean_Elab_instInhabitedMacroExpansionInfo_default;
    return v___x_892_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorIdx(mut v_x_893_: u8) -> *mut leanh::LeanObject {
    match v_x_893_ {
        0 => {
            let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_894_ = leanh::lean_unsigned_to_nat(0);
            return v___x_894_;
        }
        1 => {
            let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_895_ = leanh::lean_unsigned_to_nat(1);
            return v___x_895_;
        }
        2 => {
            let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_896_ = leanh::lean_unsigned_to_nat(2);
            return v___x_896_;
        }
        _ => {
            let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_897_ = leanh::lean_unsigned_to_nat(3);
            return v___x_897_;
        }
    }
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorIdx___boxed(
    mut v_x_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_899_: u8 = 0;
    let mut v_res_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_899_ = (leanh::lean_unbox(v_x_898_) as u8);
    v_res_900_ = l_Lean_Elab_DocElabKind_ctorIdx(v_x_boxed_899_);
    return v_res_900_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_toCtorIdx(mut v_x_901_: u8) -> *mut leanh::LeanObject {
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_902_ = l_Lean_Elab_DocElabKind_ctorIdx(v_x_901_);
    return v___x_902_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_toCtorIdx___boxed(
    mut v_x_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_904_: u8 = 0;
    let mut v_res_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_904_ = (leanh::lean_unbox(v_x_903_) as u8);
    v_res_905_ = l_Lean_Elab_DocElabKind_toCtorIdx(v_x_4__boxed_904_);
    return v_res_905_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim___redArg(
    mut v_k_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_906_);
    return v_k_906_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim___redArg___boxed(
    mut v_k_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_908_ = l_Lean_Elab_DocElabKind_ctorElim___redArg(v_k_907_);
    leanh::lean_dec(v_k_907_);
    return v_res_908_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim(
    mut v_motive_909_: *mut leanh::LeanObject,
    mut v_ctorIdx_910_: *mut leanh::LeanObject,
    mut v_t_911_: u8,
    mut v_h_912_: *mut leanh::LeanObject,
    mut v_k_913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_913_);
    return v_k_913_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_ctorElim___boxed(
    mut v_motive_914_: *mut leanh::LeanObject,
    mut v_ctorIdx_915_: *mut leanh::LeanObject,
    mut v_t_916_: *mut leanh::LeanObject,
    mut v_h_917_: *mut leanh::LeanObject,
    mut v_k_918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_919_: u8 = 0;
    let mut v_res_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_919_ = (leanh::lean_unbox(v_t_916_) as u8);
    v_res_920_ = l_Lean_Elab_DocElabKind_ctorElim(
        v_motive_914_,
        v_ctorIdx_915_,
        v_t_boxed_919_,
        v_h_917_,
        v_k_918_,
    );
    leanh::lean_dec(v_k_918_);
    leanh::lean_dec(v_ctorIdx_915_);
    return v_res_920_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim___redArg(
    mut v_role_921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_role_921_);
    return v_role_921_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim___redArg___boxed(
    mut v_role_922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_923_ = l_Lean_Elab_DocElabKind_role_elim___redArg(v_role_922_);
    leanh::lean_dec(v_role_922_);
    return v_res_923_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim(
    mut v_motive_924_: *mut leanh::LeanObject,
    mut v_t_925_: u8,
    mut v_h_926_: *mut leanh::LeanObject,
    mut v_role_927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_role_927_);
    return v_role_927_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_role_elim___boxed(
    mut v_motive_928_: *mut leanh::LeanObject,
    mut v_t_929_: *mut leanh::LeanObject,
    mut v_h_930_: *mut leanh::LeanObject,
    mut v_role_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_932_: u8 = 0;
    let mut v_res_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_932_ = (leanh::lean_unbox(v_t_929_) as u8);
    v_res_933_ =
        l_Lean_Elab_DocElabKind_role_elim(v_motive_928_, v_t_boxed_932_, v_h_930_, v_role_931_);
    leanh::lean_dec(v_role_931_);
    return v_res_933_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(
    mut v_codeBlock_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_codeBlock_934_);
    return v_codeBlock_934_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim___redArg___boxed(
    mut v_codeBlock_935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_936_ = l_Lean_Elab_DocElabKind_codeBlock_elim___redArg(v_codeBlock_935_);
    leanh::lean_dec(v_codeBlock_935_);
    return v_res_936_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim(
    mut v_motive_937_: *mut leanh::LeanObject,
    mut v_t_938_: u8,
    mut v_h_939_: *mut leanh::LeanObject,
    mut v_codeBlock_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_codeBlock_940_);
    return v_codeBlock_940_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_codeBlock_elim___boxed(
    mut v_motive_941_: *mut leanh::LeanObject,
    mut v_t_942_: *mut leanh::LeanObject,
    mut v_h_943_: *mut leanh::LeanObject,
    mut v_codeBlock_944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_945_: u8 = 0;
    let mut v_res_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_945_ = (leanh::lean_unbox(v_t_942_) as u8);
    v_res_946_ = l_Lean_Elab_DocElabKind_codeBlock_elim(
        v_motive_941_,
        v_t_boxed_945_,
        v_h_943_,
        v_codeBlock_944_,
    );
    leanh::lean_dec(v_codeBlock_944_);
    return v_res_946_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim___redArg(
    mut v_directive_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_directive_947_);
    return v_directive_947_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim___redArg___boxed(
    mut v_directive_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_949_ = l_Lean_Elab_DocElabKind_directive_elim___redArg(v_directive_948_);
    leanh::lean_dec(v_directive_948_);
    return v_res_949_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim(
    mut v_motive_950_: *mut leanh::LeanObject,
    mut v_t_951_: u8,
    mut v_h_952_: *mut leanh::LeanObject,
    mut v_directive_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_directive_953_);
    return v_directive_953_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_directive_elim___boxed(
    mut v_motive_954_: *mut leanh::LeanObject,
    mut v_t_955_: *mut leanh::LeanObject,
    mut v_h_956_: *mut leanh::LeanObject,
    mut v_directive_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_958_: u8 = 0;
    let mut v_res_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_958_ = (leanh::lean_unbox(v_t_955_) as u8);
    v_res_959_ = l_Lean_Elab_DocElabKind_directive_elim(
        v_motive_954_,
        v_t_boxed_958_,
        v_h_956_,
        v_directive_957_,
    );
    leanh::lean_dec(v_directive_957_);
    return v_res_959_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim___redArg(
    mut v_command_960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_command_960_);
    return v_command_960_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim___redArg___boxed(
    mut v_command_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Lean_Elab_DocElabKind_command_elim___redArg(v_command_961_);
    leanh::lean_dec(v_command_961_);
    return v_res_962_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim(
    mut v_motive_963_: *mut leanh::LeanObject,
    mut v_t_964_: u8,
    mut v_h_965_: *mut leanh::LeanObject,
    mut v_command_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_command_966_);
    return v_command_966_;
}
pub unsafe fn l_Lean_Elab_DocElabKind_command_elim___boxed(
    mut v_motive_967_: *mut leanh::LeanObject,
    mut v_t_968_: *mut leanh::LeanObject,
    mut v_h_969_: *mut leanh::LeanObject,
    mut v_command_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_971_: u8 = 0;
    let mut v_res_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_971_ = (leanh::lean_unbox(v_t_968_) as u8);
    v_res_972_ = l_Lean_Elab_DocElabKind_command_elim(
        v_motive_967_,
        v_t_boxed_971_,
        v_h_969_,
        v_command_970_,
    );
    leanh::lean_dec(v_command_970_);
    return v_res_972_;
}
pub unsafe fn _init_l_Lean_Elab_instReprDocElabKind_repr___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = leanh::lean_unsigned_to_nat(2);
    v___x_986_ = lean_nat_to_int(v___x_985_);
    return v___x_986_;
}
pub unsafe fn _init_l_Lean_Elab_instReprDocElabKind_repr___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = leanh::lean_unsigned_to_nat(1);
    v___x_988_ = lean_nat_to_int(v___x_987_);
    return v___x_988_;
}
pub unsafe fn l_Lean_Elab_instReprDocElabKind_repr(
    mut v_x_989_: u8,
    mut v_prec_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: u8 = 0;
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u8 = 0;
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: u8 = 0;
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_989_ {
                0 => {
                    v___x_1019_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1020_ = lean_nat_dec_le(v___x_1019_, v_prec_990_);
                    if v___x_1020_ == 0 {
                        v___x_1021_ = leanh::lean_obj_once(
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
                        v___x_1022_ = leanh::lean_obj_once(
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
                    v___x_1023_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1024_ = lean_nat_dec_le(v___x_1023_, v_prec_990_);
                    if v___x_1024_ == 0 {
                        v___x_1025_ = leanh::lean_obj_once(
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
                        v___x_1026_ = leanh::lean_obj_once(
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
                    v___x_1027_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1028_ = lean_nat_dec_le(v___x_1027_, v_prec_990_);
                    if v___x_1028_ == 0 {
                        v___x_1029_ = leanh::lean_obj_once(
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
                        v___x_1030_ = leanh::lean_obj_once(
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
                    v___x_1031_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1032_ = lean_nat_dec_le(v___x_1031_, v_prec_990_);
                    if v___x_1032_ == 0 {
                        v___x_1033_ = leanh::lean_obj_once(
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
                        v___x_1034_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_992_);
                v___x_994_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_994_, 0, v___y_992_);
                leanh::lean_ctor_set(v___x_994_, 1, v___x_993_);
                v___x_995_ = 0;
                v___x_996_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_996_, 0, v___x_994_);
                leanh::lean_ctor_set_uint8(
                    v___x_996_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_995_,
                );
                v___x_997_ = l_Repr_addAppParen(v___x_996_, v_prec_990_);
                return v___x_997_;
            }
            2 => {
                v___x_1000_ = l_Lean_Elab_instReprDocElabKind_repr___closed__3;
                leanh::lean_inc(v___y_999_);
                v___x_1001_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1001_, 0, v___y_999_);
                leanh::lean_ctor_set(v___x_1001_, 1, v___x_1000_);
                v___x_1002_ = 0;
                v___x_1003_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1003_, 0, v___x_1001_);
                leanh::lean_ctor_set_uint8(
                    v___x_1003_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1002_,
                );
                v___x_1004_ = l_Repr_addAppParen(v___x_1003_, v_prec_990_);
                return v___x_1004_;
            }
            3 => {
                v___x_1007_ = l_Lean_Elab_instReprDocElabKind_repr___closed__5;
                leanh::lean_inc(v___y_1006_);
                v___x_1008_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1008_, 0, v___y_1006_);
                leanh::lean_ctor_set(v___x_1008_, 1, v___x_1007_);
                v___x_1009_ = 0;
                v___x_1010_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1010_, 0, v___x_1008_);
                leanh::lean_ctor_set_uint8(
                    v___x_1010_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1009_,
                );
                v___x_1011_ = l_Repr_addAppParen(v___x_1010_, v_prec_990_);
                return v___x_1011_;
            }
            4 => {
                v___x_1014_ = l_Lean_Elab_instReprDocElabKind_repr___closed__7;
                leanh::lean_inc(v___y_1013_);
                v___x_1015_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1015_, 0, v___y_1013_);
                leanh::lean_ctor_set(v___x_1015_, 1, v___x_1014_);
                v___x_1016_ = 0;
                v___x_1017_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1017_, 0, v___x_1015_);
                leanh::lean_ctor_set_uint8(
                    v___x_1017_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_1035_: *mut leanh::LeanObject,
    mut v_prec_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_233__boxed_1037_: u8 = 0;
    let mut v_res_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_233__boxed_1037_ = (leanh::lean_unbox(v_x_1035_) as u8);
    v_res_1038_ = l_Lean_Elab_instReprDocElabKind_repr(v_x_233__boxed_1037_, v_prec_1036_);
    leanh::lean_dec(v_prec_1036_);
    return v_res_1038_;
}
pub unsafe fn l_Lean_Elab_Info_ctorIdx(
    mut v_x_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1041_) {
        0 => {
            let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1042_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1042_;
        }
        1 => {
            let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1043_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1043_;
        }
        2 => {
            let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1044_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1044_;
        }
        3 => {
            let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1045_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1045_;
        }
        4 => {
            let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1046_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1046_;
        }
        5 => {
            let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1047_ = leanh::lean_unsigned_to_nat(5);
            return v___x_1047_;
        }
        6 => {
            let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1048_ = leanh::lean_unsigned_to_nat(6);
            return v___x_1048_;
        }
        7 => {
            let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1049_ = leanh::lean_unsigned_to_nat(7);
            return v___x_1049_;
        }
        8 => {
            let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1050_ = leanh::lean_unsigned_to_nat(8);
            return v___x_1050_;
        }
        9 => {
            let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1051_ = leanh::lean_unsigned_to_nat(9);
            return v___x_1051_;
        }
        10 => {
            let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1052_ = leanh::lean_unsigned_to_nat(10);
            return v___x_1052_;
        }
        11 => {
            let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1053_ = leanh::lean_unsigned_to_nat(11);
            return v___x_1053_;
        }
        12 => {
            let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1054_ = leanh::lean_unsigned_to_nat(12);
            return v___x_1054_;
        }
        13 => {
            let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1055_ = leanh::lean_unsigned_to_nat(13);
            return v___x_1055_;
        }
        14 => {
            let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1056_ = leanh::lean_unsigned_to_nat(14);
            return v___x_1056_;
        }
        15 => {
            let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1057_ = leanh::lean_unsigned_to_nat(15);
            return v___x_1057_;
        }
        _ => {
            let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1058_ = leanh::lean_unsigned_to_nat(16);
            return v___x_1058_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Info_ctorIdx___boxed(
    mut v_x_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lean_Elab_Info_ctorIdx(v_x_1059_);
    leanh::lean_dec_ref(v_x_1059_);
    return v_res_1060_;
}
pub unsafe fn l_Lean_Elab_Info_ctorElim___redArg(
    mut v_t_1061_: *mut leanh::LeanObject,
    mut v_k_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1061_) == 12 {
        let mut v_i_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_i_1063_ = leanh::lean_ctor_get(v_t_1061_, 0);
        leanh::lean_inc(v_i_1063_);
        leanh::lean_dec_ref_known(v_t_1061_, 1);
        v___x_1064_ = leanh::lean_apply_1(v_k_1062_, v_i_1063_);
        return v___x_1064_;
    } else {
        let mut v_i_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_i_1065_ = leanh::lean_ctor_get(v_t_1061_, 0);
        leanh::lean_inc_ref(v_i_1065_);
        leanh::lean_dec_ref(v_t_1061_);
        v___x_1066_ = leanh::lean_apply_1(v_k_1062_, v_i_1065_);
        return v___x_1066_;
    }
}
pub unsafe fn l_Lean_Elab_Info_ctorElim(
    mut v_motive_1067_: *mut leanh::LeanObject,
    mut v_ctorIdx_1068_: *mut leanh::LeanObject,
    mut v_t_1069_: *mut leanh::LeanObject,
    mut v_h_1070_: *mut leanh::LeanObject,
    mut v_k_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1069_, v_k_1071_);
    return v___x_1072_;
}
pub unsafe fn l_Lean_Elab_Info_ctorElim___boxed(
    mut v_motive_1073_: *mut leanh::LeanObject,
    mut v_ctorIdx_1074_: *mut leanh::LeanObject,
    mut v_t_1075_: *mut leanh::LeanObject,
    mut v_h_1076_: *mut leanh::LeanObject,
    mut v_k_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Lean_Elab_Info_ctorElim(
        v_motive_1073_,
        v_ctorIdx_1074_,
        v_t_1075_,
        v_h_1076_,
        v_k_1077_,
    );
    leanh::lean_dec(v_ctorIdx_1074_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_Elab_Info_ofTacticInfo_elim___redArg(
    mut v_t_1079_: *mut leanh::LeanObject,
    mut v_ofTacticInfo_1080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1081_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1079_, v_ofTacticInfo_1080_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_Elab_Info_ofTacticInfo_elim(
    mut v_motive_1082_: *mut leanh::LeanObject,
    mut v_t_1083_: *mut leanh::LeanObject,
    mut v_h_1084_: *mut leanh::LeanObject,
    mut v_ofTacticInfo_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1083_, v_ofTacticInfo_1085_);
    return v___x_1086_;
}
pub unsafe fn l_Lean_Elab_Info_ofTermInfo_elim___redArg(
    mut v_t_1087_: *mut leanh::LeanObject,
    mut v_ofTermInfo_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1087_, v_ofTermInfo_1088_);
    return v___x_1089_;
}
pub unsafe fn l_Lean_Elab_Info_ofTermInfo_elim(
    mut v_motive_1090_: *mut leanh::LeanObject,
    mut v_t_1091_: *mut leanh::LeanObject,
    mut v_h_1092_: *mut leanh::LeanObject,
    mut v_ofTermInfo_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1091_, v_ofTermInfo_1093_);
    return v___x_1094_;
}
pub unsafe fn l_Lean_Elab_Info_ofPartialTermInfo_elim___redArg(
    mut v_t_1095_: *mut leanh::LeanObject,
    mut v_ofPartialTermInfo_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1095_, v_ofPartialTermInfo_1096_);
    return v___x_1097_;
}
pub unsafe fn l_Lean_Elab_Info_ofPartialTermInfo_elim(
    mut v_motive_1098_: *mut leanh::LeanObject,
    mut v_t_1099_: *mut leanh::LeanObject,
    mut v_h_1100_: *mut leanh::LeanObject,
    mut v_ofPartialTermInfo_1101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1099_, v_ofPartialTermInfo_1101_);
    return v___x_1102_;
}
pub unsafe fn l_Lean_Elab_Info_ofCommandInfo_elim___redArg(
    mut v_t_1103_: *mut leanh::LeanObject,
    mut v_ofCommandInfo_1104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1103_, v_ofCommandInfo_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Elab_Info_ofCommandInfo_elim(
    mut v_motive_1106_: *mut leanh::LeanObject,
    mut v_t_1107_: *mut leanh::LeanObject,
    mut v_h_1108_: *mut leanh::LeanObject,
    mut v_ofCommandInfo_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1107_, v_ofCommandInfo_1109_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_Elab_Info_ofMacroExpansionInfo_elim___redArg(
    mut v_t_1111_: *mut leanh::LeanObject,
    mut v_ofMacroExpansionInfo_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1111_, v_ofMacroExpansionInfo_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Lean_Elab_Info_ofMacroExpansionInfo_elim(
    mut v_motive_1114_: *mut leanh::LeanObject,
    mut v_t_1115_: *mut leanh::LeanObject,
    mut v_h_1116_: *mut leanh::LeanObject,
    mut v_ofMacroExpansionInfo_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1118_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1115_, v_ofMacroExpansionInfo_1117_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Elab_Info_ofOptionInfo_elim___redArg(
    mut v_t_1119_: *mut leanh::LeanObject,
    mut v_ofOptionInfo_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1119_, v_ofOptionInfo_1120_);
    return v___x_1121_;
}
pub unsafe fn l_Lean_Elab_Info_ofOptionInfo_elim(
    mut v_motive_1122_: *mut leanh::LeanObject,
    mut v_t_1123_: *mut leanh::LeanObject,
    mut v_h_1124_: *mut leanh::LeanObject,
    mut v_ofOptionInfo_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1123_, v_ofOptionInfo_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_Elab_Info_ofErrorNameInfo_elim___redArg(
    mut v_t_1127_: *mut leanh::LeanObject,
    mut v_ofErrorNameInfo_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1127_, v_ofErrorNameInfo_1128_);
    return v___x_1129_;
}
pub unsafe fn l_Lean_Elab_Info_ofErrorNameInfo_elim(
    mut v_motive_1130_: *mut leanh::LeanObject,
    mut v_t_1131_: *mut leanh::LeanObject,
    mut v_h_1132_: *mut leanh::LeanObject,
    mut v_ofErrorNameInfo_1133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1131_, v_ofErrorNameInfo_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldInfo_elim___redArg(
    mut v_t_1135_: *mut leanh::LeanObject,
    mut v_ofFieldInfo_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1135_, v_ofFieldInfo_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldInfo_elim(
    mut v_motive_1138_: *mut leanh::LeanObject,
    mut v_t_1139_: *mut leanh::LeanObject,
    mut v_h_1140_: *mut leanh::LeanObject,
    mut v_ofFieldInfo_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1139_, v_ofFieldInfo_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Lean_Elab_Info_ofCompletionInfo_elim___redArg(
    mut v_t_1143_: *mut leanh::LeanObject,
    mut v_ofCompletionInfo_1144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1143_, v_ofCompletionInfo_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Lean_Elab_Info_ofCompletionInfo_elim(
    mut v_motive_1146_: *mut leanh::LeanObject,
    mut v_t_1147_: *mut leanh::LeanObject,
    mut v_h_1148_: *mut leanh::LeanObject,
    mut v_ofCompletionInfo_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1147_, v_ofCompletionInfo_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lean_Elab_Info_ofUserWidgetInfo_elim___redArg(
    mut v_t_1151_: *mut leanh::LeanObject,
    mut v_ofUserWidgetInfo_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1151_, v_ofUserWidgetInfo_1152_);
    return v___x_1153_;
}
pub unsafe fn l_Lean_Elab_Info_ofUserWidgetInfo_elim(
    mut v_motive_1154_: *mut leanh::LeanObject,
    mut v_t_1155_: *mut leanh::LeanObject,
    mut v_h_1156_: *mut leanh::LeanObject,
    mut v_ofUserWidgetInfo_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1155_, v_ofUserWidgetInfo_1157_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_Elab_Info_ofCustomInfo_elim___redArg(
    mut v_t_1159_: *mut leanh::LeanObject,
    mut v_ofCustomInfo_1160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1159_, v_ofCustomInfo_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Elab_Info_ofCustomInfo_elim(
    mut v_motive_1162_: *mut leanh::LeanObject,
    mut v_t_1163_: *mut leanh::LeanObject,
    mut v_h_1164_: *mut leanh::LeanObject,
    mut v_ofCustomInfo_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1166_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1163_, v_ofCustomInfo_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Elab_Info_ofFVarAliasInfo_elim___redArg(
    mut v_t_1167_: *mut leanh::LeanObject,
    mut v_ofFVarAliasInfo_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1167_, v_ofFVarAliasInfo_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Elab_Info_ofFVarAliasInfo_elim(
    mut v_motive_1170_: *mut leanh::LeanObject,
    mut v_t_1171_: *mut leanh::LeanObject,
    mut v_h_1172_: *mut leanh::LeanObject,
    mut v_ofFVarAliasInfo_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1174_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1171_, v_ofFVarAliasInfo_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldRedeclInfo_elim___redArg(
    mut v_t_1175_: *mut leanh::LeanObject,
    mut v_ofFieldRedeclInfo_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1175_, v_ofFieldRedeclInfo_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Elab_Info_ofFieldRedeclInfo_elim(
    mut v_motive_1178_: *mut leanh::LeanObject,
    mut v_t_1179_: *mut leanh::LeanObject,
    mut v_h_1180_: *mut leanh::LeanObject,
    mut v_ofFieldRedeclInfo_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1179_, v_ofFieldRedeclInfo_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Lean_Elab_Info_ofDelabTermInfo_elim___redArg(
    mut v_t_1183_: *mut leanh::LeanObject,
    mut v_ofDelabTermInfo_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1183_, v_ofDelabTermInfo_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Lean_Elab_Info_ofDelabTermInfo_elim(
    mut v_motive_1186_: *mut leanh::LeanObject,
    mut v_t_1187_: *mut leanh::LeanObject,
    mut v_h_1188_: *mut leanh::LeanObject,
    mut v_ofDelabTermInfo_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1187_, v_ofDelabTermInfo_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Lean_Elab_Info_ofChoiceInfo_elim___redArg(
    mut v_t_1191_: *mut leanh::LeanObject,
    mut v_ofChoiceInfo_1192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1191_, v_ofChoiceInfo_1192_);
    return v___x_1193_;
}
pub unsafe fn l_Lean_Elab_Info_ofChoiceInfo_elim(
    mut v_motive_1194_: *mut leanh::LeanObject,
    mut v_t_1195_: *mut leanh::LeanObject,
    mut v_h_1196_: *mut leanh::LeanObject,
    mut v_ofChoiceInfo_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1195_, v_ofChoiceInfo_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocInfo_elim___redArg(
    mut v_t_1199_: *mut leanh::LeanObject,
    mut v_ofDocInfo_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1199_, v_ofDocInfo_1200_);
    return v___x_1201_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocInfo_elim(
    mut v_motive_1202_: *mut leanh::LeanObject,
    mut v_t_1203_: *mut leanh::LeanObject,
    mut v_h_1204_: *mut leanh::LeanObject,
    mut v_ofDocInfo_1205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1203_, v_ofDocInfo_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocElabInfo_elim___redArg(
    mut v_t_1207_: *mut leanh::LeanObject,
    mut v_ofDocElabInfo_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1209_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1207_, v_ofDocElabInfo_1208_);
    return v___x_1209_;
}
pub unsafe fn l_Lean_Elab_Info_ofDocElabInfo_elim(
    mut v_motive_1210_: *mut leanh::LeanObject,
    mut v_t_1211_: *mut leanh::LeanObject,
    mut v_h_1212_: *mut leanh::LeanObject,
    mut v_ofDocElabInfo_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = l_Lean_Elab_Info_ctorElim___redArg(v_t_1211_, v_ofDocElabInfo_1213_);
    return v___x_1214_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfo_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1215_ = l_Lean_Elab_instInhabitedTacticInfo_default;
    v___x_1216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1216_, 0, v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfo_default() -> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1217_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfo_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfo_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedInfo_default___closed__0,
    );
    return v___x_1217_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfo() -> *mut leanh::LeanObject {
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ = l_Lean_Elab_instInhabitedInfo_default;
    return v___x_1218_;
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorIdx(
    mut v_x_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1219_) {
        0 => {
            let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1220_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1220_;
        }
        1 => {
            let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1221_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1221_;
        }
        _ => {
            let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1222_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1222_;
        }
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorIdx___boxed(
    mut v_x_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Lean_Elab_InfoTree_ctorIdx(v_x_1223_);
    leanh::lean_dec_ref(v_x_1223_);
    return v_res_1224_;
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorElim___redArg(
    mut v_t_1225_: *mut leanh::LeanObject,
    mut v_k_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1225_) == 2 {
        let mut v_mvarId_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_1227_ = leanh::lean_ctor_get(v_t_1225_, 0);
        leanh::lean_inc(v_mvarId_1227_);
        leanh::lean_dec_ref_known(v_t_1225_, 1);
        v___x_1228_ = leanh::lean_apply_1(v_k_1226_, v_mvarId_1227_);
        return v___x_1228_;
    } else {
        let mut v_i_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_t_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_i_1229_ = leanh::lean_ctor_get(v_t_1225_, 0);
        leanh::lean_inc_ref(v_i_1229_);
        v_t_1230_ = leanh::lean_ctor_get(v_t_1225_, 1);
        leanh::lean_inc_ref(v_t_1230_);
        leanh::lean_dec_ref(v_t_1225_);
        v___x_1231_ = leanh::lean_apply_2(v_k_1226_, v_i_1229_, v_t_1230_);
        return v___x_1231_;
    }
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorElim(
    mut v_motive__1_1232_: *mut leanh::LeanObject,
    mut v_ctorIdx_1233_: *mut leanh::LeanObject,
    mut v_t_1234_: *mut leanh::LeanObject,
    mut v_h_1235_: *mut leanh::LeanObject,
    mut v_k_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1234_, v_k_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Lean_Elab_InfoTree_ctorElim___boxed(
    mut v_motive__1_1238_: *mut leanh::LeanObject,
    mut v_ctorIdx_1239_: *mut leanh::LeanObject,
    mut v_t_1240_: *mut leanh::LeanObject,
    mut v_h_1241_: *mut leanh::LeanObject,
    mut v_k_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Lean_Elab_InfoTree_ctorElim(
        v_motive__1_1238_,
        v_ctorIdx_1239_,
        v_t_1240_,
        v_h_1241_,
        v_k_1242_,
    );
    leanh::lean_dec(v_ctorIdx_1239_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_Elab_InfoTree_context_elim___redArg(
    mut v_t_1244_: *mut leanh::LeanObject,
    mut v_context_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1244_, v_context_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Lean_Elab_InfoTree_context_elim(
    mut v_motive__1_1247_: *mut leanh::LeanObject,
    mut v_t_1248_: *mut leanh::LeanObject,
    mut v_h_1249_: *mut leanh::LeanObject,
    mut v_context_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1248_, v_context_1250_);
    return v___x_1251_;
}
pub unsafe fn l_Lean_Elab_InfoTree_node_elim___redArg(
    mut v_t_1252_: *mut leanh::LeanObject,
    mut v_node_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1252_, v_node_1253_);
    return v___x_1254_;
}
pub unsafe fn l_Lean_Elab_InfoTree_node_elim(
    mut v_motive__1_1255_: *mut leanh::LeanObject,
    mut v_t_1256_: *mut leanh::LeanObject,
    mut v_h_1257_: *mut leanh::LeanObject,
    mut v_node_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1259_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1256_, v_node_1258_);
    return v___x_1259_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hole_elim___redArg(
    mut v_t_1260_: *mut leanh::LeanObject,
    mut v_hole_1261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1260_, v_hole_1261_);
    return v___x_1262_;
}
pub unsafe fn l_Lean_Elab_InfoTree_hole_elim(
    mut v_motive__1_1263_: *mut leanh::LeanObject,
    mut v_t_1264_: *mut leanh::LeanObject,
    mut v_h_1265_: *mut leanh::LeanObject,
    mut v_hole_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_Lean_Elab_InfoTree_ctorElim___redArg(v_t_1264_, v_hole_1266_);
    return v___x_1267_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1268_ = l_Lean_instInhabitedPersistentArray_default(leanh::lean_box(0));
    return v___x_1268_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__0,
    );
    v___x_1270_ = l_Lean_Elab_instInhabitedInfo_default;
    v___x_1271_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
    leanh::lean_ctor_set(v___x_1271_, 1, v___x_1269_);
    return v___x_1271_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree_default() -> *mut leanh::LeanObject {
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoTree_default___closed__1_once),
        _init_l_Lean_Elab_instInhabitedInfoTree_default___closed__1,
    );
    return v___x_1272_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoTree() -> *mut leanh::LeanObject {
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Lean_Elab_instInhabitedInfoTree_default;
    return v___x_1273_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1274_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1275_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__0_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__0,
    );
    v___x_1276_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1276_, 0, v___x_1275_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = leanh::lean_unsigned_to_nat(32);
    v___x_1278_ = lean_mk_empty_array_with_capacity(v___x_1277_);
    v___x_1279_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1279_, 0, v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1280_: usize = 0;
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1280_ = 5usize;
    v___x_1281_ = leanh::lean_unsigned_to_nat(0);
    v___x_1282_ = leanh::lean_unsigned_to_nat(32);
    v___x_1283_ = lean_mk_empty_array_with_capacity(v___x_1282_);
    v___x_1284_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__2_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__2,
    );
    v___x_1285_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1285_, 0, v___x_1284_);
    leanh::lean_ctor_set(v___x_1285_, 1, v___x_1283_);
    leanh::lean_ctor_set(v___x_1285_, 2, v___x_1281_);
    leanh::lean_ctor_set(v___x_1285_, 3, v___x_1281_);
    leanh::lean_ctor_set_usize(v___x_1285_, 4, v___x_1280_);
    return v___x_1285_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__3_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__3,
    );
    v___x_1287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__1_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__1,
    );
    v___x_1288_ = 1;
    v___x_1289_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1287_);
    leanh::lean_ctor_set(v___x_1289_, 1, v___x_1287_);
    leanh::lean_ctor_set(v___x_1289_, 2, v___x_1286_);
    leanh::lean_ctor_set_uint8(
        v___x_1289_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_1288_,
    );
    return v___x_1289_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState_default() -> *mut leanh::LeanObject {
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_instInhabitedInfoState_default___closed__4_once),
        _init_l_Lean_Elab_instInhabitedInfoState_default___closed__4,
    );
    return v___x_1290_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedInfoState() -> *mut leanh::LeanObject {
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Elab_instInhabitedInfoState_default;
    return v___x_1291_;
}
pub unsafe fn l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0(
    mut v_modifyInfoState_1292_: *mut leanh::LeanObject,
    mut v_inst_1293_: *mut leanh::LeanObject,
    mut v_f_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ = leanh::lean_apply_1(v_modifyInfoState_1292_, v_f_1294_);
    v___x_1296_ = leanh::lean_apply_2(v_inst_1293_, leanh::lean_box(0), v___x_1295_);
    return v___x_1296_;
}
pub unsafe fn l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(
    mut v_inst_1297_: *mut leanh::LeanObject,
    mut v_inst_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getInfoState_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyInfoState_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___f_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getInfoState_1299_ = leanh::lean_ctor_get(v_inst_1298_, 0);
                v_modifyInfoState_1300_ = leanh::lean_ctor_get(v_inst_1298_, 1);
                v_isSharedCheck_1309_ = (!leanh::lean_is_exclusive(v_inst_1298_)) as u8;
                if v_isSharedCheck_1309_ == 0 {
                    v___x_1302_ = v_inst_1298_;
                    v_isShared_1303_ = v_isSharedCheck_1309_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyInfoState_1300_);
                    leanh::lean_inc(v_getInfoState_1299_);
                    leanh::lean_dec(v_inst_1298_);
                    v___x_1302_ = leanh::lean_box(0);
                    v_isShared_1303_ = v_isSharedCheck_1309_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_inst_1297_);
                v___f_1304_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1304_, 0, v_modifyInfoState_1300_);
                leanh::lean_closure_set(v___f_1304_, 1, v_inst_1297_);
                v___x_1305_ = leanh::lean_apply_2(
                    v_inst_1297_,
                    leanh::lean_box(0),
                    v_getInfoState_1299_,
                );
                if v_isShared_1303_ == 0 {
                    leanh::lean_ctor_set(v___x_1302_, 1, v___f_1304_);
                    leanh::lean_ctor_set(v___x_1302_, 0, v___x_1305_);
                    v___x_1307_ = v___x_1302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___f_1304_);
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
    mut v_m_1310_: *mut leanh::LeanObject,
    mut v_n_1311_: *mut leanh::LeanObject,
    mut v_inst_1312_: *mut leanh::LeanObject,
    mut v_inst_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v_inst_1312_, v_inst_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Lean_Elab_setInfoState___redArg___lam__0(
    mut v_s_1315_: *mut leanh::LeanObject,
    mut v_x_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_s_1315_);
    return v_s_1315_;
}
pub unsafe fn l_Lean_Elab_setInfoState___redArg___lam__0___boxed(
    mut v_s_1317_: *mut leanh::LeanObject,
    mut v_x_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Lean_Elab_setInfoState___redArg___lam__0(v_s_1317_, v_x_1318_);
    leanh::lean_dec_ref(v_x_1318_);
    leanh::lean_dec_ref(v_s_1317_);
    return v_res_1319_;
}
pub unsafe fn l_Lean_Elab_setInfoState___redArg(
    mut v_inst_1320_: *mut leanh::LeanObject,
    mut v_s_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyInfoState_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyInfoState_1322_ = leanh::lean_ctor_get(v_inst_1320_, 1);
    leanh::lean_inc(v_modifyInfoState_1322_);
    leanh::lean_dec_ref(v_inst_1320_);
    v___f_1323_ = leanh::lean_alloc_closure(
        l_Lean_Elab_setInfoState___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1323_, 0, v_s_1321_);
    v___x_1324_ = leanh::lean_apply_1(v_modifyInfoState_1322_, v___f_1323_);
    return v___x_1324_;
}
pub unsafe fn l_Lean_Elab_setInfoState(
    mut v_m_1325_: *mut leanh::LeanObject,
    mut v_inst_1326_: *mut leanh::LeanObject,
    mut v_s_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1328_ = l_Lean_Elab_setInfoState___redArg(v_inst_1326_, v_s_1327_);
    return v___x_1328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_InfoTree_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_OpenDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PPContext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_MetavarContext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedTermInfo_default = _init_l_Lean_Elab_instInhabitedTermInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo_default);
    l_Lean_Elab_instInhabitedTermInfo = _init_l_Lean_Elab_instInhabitedTermInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo);
    l_Lean_Elab_instInhabitedPartialTermInfo_default =
        _init_l_Lean_Elab_instInhabitedPartialTermInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo_default);
    l_Lean_Elab_instInhabitedPartialTermInfo = _init_l_Lean_Elab_instInhabitedPartialTermInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo);
    l_Lean_Elab_instInhabitedFieldInfo_default = _init_l_Lean_Elab_instInhabitedFieldInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo_default);
    l_Lean_Elab_instInhabitedFieldInfo = _init_l_Lean_Elab_instInhabitedFieldInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo);
    l_Lean_Elab_instInhabitedTacticInfo_default =
        _init_l_Lean_Elab_instInhabitedTacticInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo_default);
    l_Lean_Elab_instInhabitedTacticInfo = _init_l_Lean_Elab_instInhabitedTacticInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo);
    l_Lean_Elab_instInhabitedMacroExpansionInfo_default =
        _init_l_Lean_Elab_instInhabitedMacroExpansionInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo_default);
    l_Lean_Elab_instInhabitedMacroExpansionInfo =
        _init_l_Lean_Elab_instInhabitedMacroExpansionInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo);
    l_Lean_Elab_instInhabitedInfo_default = _init_l_Lean_Elab_instInhabitedInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfo_default);
    l_Lean_Elab_instInhabitedInfo = _init_l_Lean_Elab_instInhabitedInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfo);
    l_Lean_Elab_instInhabitedInfoTree_default = _init_l_Lean_Elab_instInhabitedInfoTree_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree_default);
    l_Lean_Elab_instInhabitedInfoTree = _init_l_Lean_Elab_instInhabitedInfoTree();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree);
    l_Lean_Elab_instInhabitedInfoState_default = _init_l_Lean_Elab_instInhabitedInfoState_default();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState_default);
    l_Lean_Elab_instInhabitedInfoState = _init_l_Lean_Elab_instInhabitedInfoState();
    leanh::lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_InfoTree_Types(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_InfoTree_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_OpenDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PPContext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_MetavarContext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Environment(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Widget_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_InfoTree_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_InfoTree_Types(builtin);
}