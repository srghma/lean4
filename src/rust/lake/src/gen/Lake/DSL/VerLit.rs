// Lean compiler output
// Module: Lake.DSL.VerLit
// Imports: Lean.ToExpr Lake.Util.Version Lake.DSL.Syntax Lean.Meta.Eval
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity, lean_st_ref_get};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lake::Util::Version::{
    initialize_Lake_Util_Version, runtime_initialize_Lake_Util_Version,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType, l_Lean_Elab_Term_termElabAttribute,
    l_Lean_Elab_Term_tryPostponeIfNoneOrMVar,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkStrLit};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppM;
use crate::r#gen::Lean::Meta::Eval::{
    initialize_Lean_Meta_Eval, l_Lean_Meta_evalExpr___redArg, runtime_initialize_Lean_Meta_Eval,
};
use crate::r#gen::Lean::ToExpr::{initialize_Lean_ToExpr, runtime_initialize_Lean_ToExpr};
pub static l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 97, 107, 101, 0],
};
static mut l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_instToExprSemVerCore___lam__0___closed__1_value:
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
    m_data: [83, 101, 109, 86, 101, 114, 67, 111, 114, 101, 0],
};
static mut l_Lake_DSL_instToExprSemVerCore___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_DSL_instToExprSemVerCore___lam__0___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_DSL_instToExprSemVerCore___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        8154920839922976315 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3_value:
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        9780025012847184991 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_instToExprSemVerCore___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_DSL_instToExprSemVerCore___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_DSL_instToExprSemVerCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_instToExprSemVerCore___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_instToExprSemVerCore___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
            8154920839922976315 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_instToExprSemVerCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_instToExprSemVerCore___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_instToExprSemVerCore___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_instToExprSemVerCore___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_instToExprSemVerCore___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_instToExprSemVerCore: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_instToExprStdVer___lam__0___closed__0_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [83, 116, 100, 86, 101, 114, 0],
};
static mut l_Lake_DSL_instToExprStdVer___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_instToExprStdVer___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l_Lake_DSL_instToExprStdVer___lam__0___closed__1_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___lam__0___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        11402519319361589889 as *mut leanh::LeanObject,
    ],
};
pub static l_Lake_DSL_instToExprStdVer___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___lam__0___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
            14475527532111846157 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_instToExprStdVer___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_instToExprStdVer___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_instToExprStdVer___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_DSL_instToExprStdVer___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_DSL_instToExprStdVer___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_DSL_instToExprStdVer___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lake_DSL_instToExprStdVer___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            13012506173997729135 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lake_DSL_instToExprStdVer___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            11402519319361589889 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_DSL_instToExprStdVer___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_DSL_instToExprStdVer___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_DSL_instToExprStdVer___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_instToExprStdVer___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_DSL_instToExprStdVer___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_DSL_instToExprStdVer___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_DSL_instToExprStdVer: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [68, 83, 76, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__1_value:
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
    m_data: [118, 101, 114, 76, 105, 116, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__1_value)
        as *mut leanh::LeanObject;
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__0_value)
            as *mut leanh::LeanObject,
        5901868804703194544 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__1_value)
            as *mut leanh::LeanObject,
        9704141730406518167 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__3_value:
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
    m_data: [69, 120, 99, 101, 112, 116, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__4_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__3_value)
            as *mut leanh::LeanObject,
        15197845462264082926 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__5_value:
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
    m_data: [83, 116, 114, 105, 110, 103, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__6_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__5_value)
            as *mut leanh::LeanObject,
        3136308715950998022 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__6_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__9_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__10_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__10_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__11_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__11_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__12_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__12_value)
        as *mut leanh::LeanObject;
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__9_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__10_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value_aux_2:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__11_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__12_value)
            as *mut leanh::LeanObject,
        12966880221525079621 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__14_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 111, 100, 101, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__14_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__16_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__14_value)
            as *mut leanh::LeanObject,
        8360807984477385524 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__16_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__17_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        68, 101, 99, 111, 100, 101, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__17_value)
        as *mut leanh::LeanObject;
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__17_value)
            as *mut leanh::LeanObject,
        8006748460213007062 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__14_value)
            as *mut leanh::LeanObject,
        10795348008563601213 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__19_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__18_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__19_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__20_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__19_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__20_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__21_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__21_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__22_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__21_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__22_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__23_value:
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
    m_data: [116, 101, 114, 109, 83, 33, 95, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__23_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__24_value:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__23_value)
            as *mut leanh::LeanObject,
        11081549158230622750 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__24_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__25_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [115, 33, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__25_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__26_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 120, 112, 114, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__26_value)
        as *mut leanh::LeanObject;
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__27_value_aux_0:
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
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__9_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__27_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__27_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__26_value)
            as *mut leanh::LeanObject,
        5933584171502587988 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__27_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__28:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__30_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [116, 111, 82, 101, 115, 117, 108, 116, 69, 120, 112, 114, 0],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__30_value)
        as *mut leanh::LeanObject;
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        13012506173997729135 as *mut leanh::LeanObject,
    ],
};
static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__0_value)
            as *mut leanh::LeanObject,
        5901868804703194544 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__30_value)
            as *mut leanh::LeanObject,
        7621744686212546764 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__32_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111,
        116, 32, 107, 110, 111, 119, 110, 0,
    ],
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__32:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__32_value)
        as *mut leanh::LeanObject;
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__0_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value) as *mut leanh::LeanObject,12997130533650095963 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__0_value) as *mut leanh::LeanObject,11286550318989764116 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [86, 101, 114, 76, 105, 116, 0]};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__4_value) as *mut leanh::LeanObject,1646967539432975521 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__5_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,144483742107491140 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__0_value) as *mut leanh::LeanObject,3796146304896796412 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__0_value) as *mut leanh::LeanObject,10362313147755499935 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__9_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 86, 101, 114, 76, 105, 116, 0]};
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__9_value) as *mut leanh::LeanObject,4524756463937128807 as *mut leanh::LeanObject] };
static mut l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__10_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = leanh::lean_box(0);
    v___x_541_ = l_Lake_DSL_instToExprSemVerCore___lam__0___closed__3;
    v___x_542_ = l_Lean_mkConst(v___x_541_, v___x_540_);
    return v___x_542_;
}
pub unsafe fn l_Lake_DSL_instToExprSemVerCore___lam__0(
    mut v_ver_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_major_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minor_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patch_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_major_544_ = leanh::lean_ctor_get(v_ver_543_, 0);
    leanh::lean_inc(v_major_544_);
    v_minor_545_ = leanh::lean_ctor_get(v_ver_543_, 1);
    leanh::lean_inc(v_minor_545_);
    v_patch_546_ = leanh::lean_ctor_get(v_ver_543_, 2);
    leanh::lean_inc(v_patch_546_);
    leanh::lean_dec_ref(v_ver_543_);
    v___x_547_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4_once),
        _init_l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4,
    );
    v___x_548_ = l_Lean_mkNatLit(v_major_544_);
    v___x_549_ = l_Lean_mkNatLit(v_minor_545_);
    v___x_550_ = l_Lean_mkNatLit(v_patch_546_);
    v___x_551_ = leanh::lean_unsigned_to_nat(3);
    v___x_552_ = lean_mk_empty_array_with_capacity(v___x_551_);
    v___x_553_ = lean_array_push(v___x_552_, v___x_548_);
    v___x_554_ = lean_array_push(v___x_553_, v___x_549_);
    v___x_555_ = lean_array_push(v___x_554_, v___x_550_);
    v___x_556_ = l_Lean_mkAppN(v___x_547_, v___x_555_);
    leanh::lean_dec_ref(v___x_555_);
    return v___x_556_;
}
pub unsafe fn _init_l_Lake_DSL_instToExprSemVerCore___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = leanh::lean_box(0);
    v___x_562_ = l_Lake_DSL_instToExprSemVerCore___closed__1;
    v___x_563_ = l_Lean_mkConst(v___x_562_, v___x_561_);
    return v___x_563_;
}
pub unsafe fn _init_l_Lake_DSL_instToExprSemVerCore___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___closed__2_once),
        _init_l_Lake_DSL_instToExprSemVerCore___closed__2,
    );
    v___f_565_ = l_Lake_DSL_instToExprSemVerCore___closed__0;
    v___x_566_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_566_, 0, v___f_565_);
    leanh::lean_ctor_set(v___x_566_, 1, v___x_564_);
    return v___x_566_;
}
pub unsafe fn _init_l_Lake_DSL_instToExprSemVerCore() -> *mut leanh::LeanObject {
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___closed__3_once),
        _init_l_Lake_DSL_instToExprSemVerCore___closed__3,
    );
    return v___x_567_;
}
pub unsafe fn _init_l_Lake_DSL_instToExprStdVer___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = leanh::lean_box(0);
    v___x_574_ = l_Lake_DSL_instToExprStdVer___lam__0___closed__1;
    v___x_575_ = l_Lean_mkConst(v___x_574_, v___x_573_);
    return v___x_575_;
}
pub unsafe fn l_Lake_DSL_instToExprStdVer___lam__0(
    mut v_ver_576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemVerCore_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_major_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minor_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patch_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSemVerCore_577_ = leanh::lean_ctor_get(v_ver_576_, 0);
    leanh::lean_inc_ref(v_toSemVerCore_577_);
    v_specialDescr_578_ = leanh::lean_ctor_get(v_ver_576_, 1);
    leanh::lean_inc_ref(v_specialDescr_578_);
    leanh::lean_dec_ref(v_ver_576_);
    v_major_579_ = leanh::lean_ctor_get(v_toSemVerCore_577_, 0);
    leanh::lean_inc(v_major_579_);
    v_minor_580_ = leanh::lean_ctor_get(v_toSemVerCore_577_, 1);
    leanh::lean_inc(v_minor_580_);
    v_patch_581_ = leanh::lean_ctor_get(v_toSemVerCore_577_, 2);
    leanh::lean_inc(v_patch_581_);
    leanh::lean_dec_ref(v_toSemVerCore_577_);
    v___x_582_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprStdVer___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprStdVer___lam__0___closed__2_once),
        _init_l_Lake_DSL_instToExprStdVer___lam__0___closed__2,
    );
    v___x_583_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4_once),
        _init_l_Lake_DSL_instToExprSemVerCore___lam__0___closed__4,
    );
    v___x_584_ = l_Lean_mkNatLit(v_major_579_);
    v___x_585_ = l_Lean_mkNatLit(v_minor_580_);
    v___x_586_ = l_Lean_mkNatLit(v_patch_581_);
    v___x_587_ = leanh::lean_unsigned_to_nat(3);
    v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
    v___x_589_ = lean_array_push(v___x_588_, v___x_584_);
    v___x_590_ = lean_array_push(v___x_589_, v___x_585_);
    v___x_591_ = lean_array_push(v___x_590_, v___x_586_);
    v___x_592_ = l_Lean_mkAppN(v___x_583_, v___x_591_);
    leanh::lean_dec_ref(v___x_591_);
    v___x_593_ = l_Lean_mkStrLit(v_specialDescr_578_);
    v___x_594_ = leanh::lean_unsigned_to_nat(2);
    v___x_595_ = lean_mk_empty_array_with_capacity(v___x_594_);
    v___x_596_ = lean_array_push(v___x_595_, v___x_592_);
    v___x_597_ = lean_array_push(v___x_596_, v___x_593_);
    v___x_598_ = l_Lean_mkAppN(v___x_582_, v___x_597_);
    leanh::lean_dec_ref(v___x_597_);
    return v___x_598_;
}
pub unsafe fn _init_l_Lake_DSL_instToExprStdVer___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = leanh::lean_box(0);
    v___x_604_ = l_Lake_DSL_instToExprStdVer___closed__1;
    v___x_605_ = l_Lean_mkConst(v___x_604_, v___x_603_);
    return v___x_605_;
}
pub unsafe fn _init_l_Lake_DSL_instToExprStdVer___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprStdVer___closed__2),
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprStdVer___closed__2_once),
        _init_l_Lake_DSL_instToExprStdVer___closed__2,
    );
    v___f_607_ = l_Lake_DSL_instToExprStdVer___closed__0;
    v___x_608_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_608_, 0, v___f_607_);
    leanh::lean_ctor_set(v___x_608_, 1, v___x_606_);
    return v___x_608_;
}
pub unsafe fn _init_l_Lake_DSL_instToExprStdVer() -> *mut leanh::LeanObject {
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprStdVer___closed__3),
        core::ptr::addr_of_mut!(l_Lake_DSL_instToExprStdVer___closed__3_once),
        _init_l_Lake_DSL_instToExprStdVer___closed__3,
    );
    return v___x_609_;
}
pub unsafe fn l_Lake_DSL_toResultExpr___redArg(
    mut v_inst_610_: *mut leanh::LeanObject,
    mut v_x_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_toExpr_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_624_: u8 = 0;
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_611_) == 0 {
                    leanh::lean_dec_ref(v_inst_610_);
                    v_a_612_ = leanh::lean_ctor_get(v_x_611_, 0);
                    v_isSharedCheck_619_ = (!leanh::lean_is_exclusive(v_x_611_)) as u8;
                    if v_isSharedCheck_619_ == 0 {
                        v___x_614_ = v_x_611_;
                        v_isShared_615_ = v_isSharedCheck_619_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_612_);
                        leanh::lean_dec(v_x_611_);
                        v___x_614_ = leanh::lean_box(0);
                        v_isShared_615_ = v_isSharedCheck_619_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_toExpr_620_ = leanh::lean_ctor_get(v_inst_610_, 0);
                    leanh::lean_inc_ref(v_toExpr_620_);
                    leanh::lean_dec_ref(v_inst_610_);
                    v_a_621_ = leanh::lean_ctor_get(v_x_611_, 0);
                    v_isSharedCheck_629_ = (!leanh::lean_is_exclusive(v_x_611_)) as u8;
                    if v_isSharedCheck_629_ == 0 {
                        v___x_623_ = v_x_611_;
                        v_isShared_624_ = v_isSharedCheck_629_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_621_);
                        leanh::lean_dec(v_x_611_);
                        v___x_623_ = leanh::lean_box(0);
                        v_isShared_624_ = v_isSharedCheck_629_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_615_ == 0 {
                    v___x_617_ = v___x_614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
                    v___x_617_ = v_reuseFailAlloc_618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_617_;
            }
            3 => {
                v___x_625_ = leanh::lean_apply_1(v_toExpr_620_, v_a_621_);
                if v_isShared_624_ == 0 {
                    leanh::lean_ctor_set(v___x_623_, 0, v___x_625_);
                    v___x_627_ = v___x_623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
                    v___x_627_ = v_reuseFailAlloc_628_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_DSL_toResultExpr(
    mut v_00_u03b1_630_: *mut leanh::LeanObject,
    mut v_inst_631_: *mut leanh::LeanObject,
    mut v_x_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_633_ = l_Lake_DSL_toResultExpr___redArg(v_inst_631_, v_x_632_);
    return v___x_633_;
}
pub unsafe fn l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_unsafe__1(
    mut v_resT_634_: *mut leanh::LeanObject,
    mut v_resE_635_: *mut leanh::LeanObject,
    mut v_a_636_: *mut leanh::LeanObject,
    mut v_a_637_: *mut leanh::LeanObject,
    mut v_a_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_641_: u8 = 0;
    let mut v___x_642_: u8 = 0;
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_641_ = 1;
    v___x_642_ = 1;
    v___x_643_ = l_Lean_Meta_evalExpr___redArg(
        v_resT_634_,
        v_resE_635_,
        v___x_641_,
        v___x_642_,
        v_a_636_,
        v_a_637_,
        v_a_638_,
        v_a_639_,
    );
    return v___x_643_;
}
pub unsafe fn l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_unsafe__1___boxed(
    mut v_resT_644_: *mut leanh::LeanObject,
    mut v_resE_645_: *mut leanh::LeanObject,
    mut v_a_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
    mut v_a_648_: *mut leanh::LeanObject,
    mut v_a_649_: *mut leanh::LeanObject,
    mut v_a_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_651_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_unsafe__1(
        v_resT_644_,
        v_resE_645_,
        v_a_646_,
        v_a_647_,
        v_a_648_,
        v_a_649_,
    );
    leanh::lean_dec(v_a_649_);
    leanh::lean_dec_ref(v_a_648_);
    leanh::lean_dec(v_a_647_);
    leanh::lean_dec_ref(v_a_646_);
    return v_res_651_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = leanh::lean_box(0);
    v___x_653_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_654_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_654_, 0, v___x_653_);
    leanh::lean_ctor_set(v___x_654_, 1, v___x_652_);
    return v___x_654_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg___closed__0);
    v___x_657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_657_, 0, v___x_656_);
    return v___x_657_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg___boxed(
    mut v___y_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_659_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg();
    return v_res_659_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0(
    mut v_00_u03b1_660_: *mut leanh::LeanObject,
    mut v___y_661_: *mut leanh::LeanObject,
    mut v___y_662_: *mut leanh::LeanObject,
    mut v___y_663_: *mut leanh::LeanObject,
    mut v___y_664_: *mut leanh::LeanObject,
    mut v___y_665_: *mut leanh::LeanObject,
    mut v___y_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg();
    return v___x_668_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___boxed(
    mut v_00_u03b1_669_: *mut leanh::LeanObject,
    mut v___y_670_: *mut leanh::LeanObject,
    mut v___y_671_: *mut leanh::LeanObject,
    mut v___y_672_: *mut leanh::LeanObject,
    mut v___y_673_: *mut leanh::LeanObject,
    mut v___y_674_: *mut leanh::LeanObject,
    mut v___y_675_: *mut leanh::LeanObject,
    mut v___y_676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0(v_00_u03b1_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
    leanh::lean_dec(v___y_675_);
    leanh::lean_dec_ref(v___y_674_);
    leanh::lean_dec(v___y_673_);
    leanh::lean_dec_ref(v___y_672_);
    leanh::lean_dec(v___y_671_);
    leanh::lean_dec_ref(v___y_670_);
    return v_res_677_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = leanh::lean_box(1);
    v___x_679_ = l_Lean_MessageData_ofFormat(v___x_678_);
    return v___x_679_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__2;
    v___x_684_ = l_Lean_MessageData_ofFormat(v___x_683_);
    return v___x_684_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4(
    mut v_x_685_: *mut leanh::LeanObject,
    mut v_x_686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v_before_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_695_: u8 = 0;
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_unused_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_686_) == 0 {
                    return v_x_685_;
                } else {
                    v_head_687_ = leanh::lean_ctor_get(v_x_686_, 0);
                    v_tail_688_ = leanh::lean_ctor_get(v_x_686_, 1);
                    v_isSharedCheck_710_ = (!leanh::lean_is_exclusive(v_x_686_)) as u8;
                    if v_isSharedCheck_710_ == 0 {
                        v___x_690_ = v_x_686_;
                        v_isShared_691_ = v_isSharedCheck_710_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_688_);
                        leanh::lean_inc(v_head_687_);
                        leanh::lean_dec(v_x_686_);
                        v___x_690_ = leanh::lean_box(0);
                        v_isShared_691_ = v_isSharedCheck_710_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_692_ = leanh::lean_ctor_get(v_head_687_, 0);
                v_isSharedCheck_708_ = (!leanh::lean_is_exclusive(v_head_687_)) as u8;
                if v_isSharedCheck_708_ == 0 {
                    v_unused_709_ = leanh::lean_ctor_get(v_head_687_, 1);
                    leanh::lean_dec(v_unused_709_);
                    v___x_694_ = v_head_687_;
                    v_isShared_695_ = v_isSharedCheck_708_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_692_);
                    leanh::lean_dec(v_head_687_);
                    v___x_694_ = leanh::lean_box(0);
                    v_isShared_695_ = v_isSharedCheck_708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_695_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_694_, 7);
                    leanh::lean_ctor_set(v___x_694_, 1, v___x_696_);
                    leanh::lean_ctor_set(v___x_694_, 0, v_x_685_);
                    v___x_698_ = v___x_694_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_x_685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_696_);
                    v___x_698_ = v_reuseFailAlloc_707_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_699_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__3);
                if v_isShared_691_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_690_, 7);
                    leanh::lean_ctor_set(v___x_690_, 1, v___x_699_);
                    leanh::lean_ctor_set(v___x_690_, 0, v___x_698_);
                    v___x_701_ = v___x_690_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_706_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_699_);
                    v___x_701_ = v_reuseFailAlloc_706_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_702_ = l_Lean_MessageData_ofSyntax(v_before_692_);
                v___x_703_ = l_Lean_indentD(v___x_702_);
                v___x_704_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_704_, 0, v___x_701_);
                leanh::lean_ctor_set(v___x_704_, 1, v___x_703_);
                v_x_685_ = v___x_704_;
                v_x_686_ = v_tail_688_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__3(
    mut v_opts_711_: *mut leanh::LeanObject,
    mut v_opt_712_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_713_ = leanh::lean_ctor_get(v_opt_712_, 0);
    v_defValue_714_ = leanh::lean_ctor_get(v_opt_712_, 1);
    v_map_715_ = leanh::lean_ctor_get(v_opts_711_, 0);
    v___x_716_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_715_,
            v_name_713_,
        );
    if leanh::lean_obj_tag(v___x_716_) == 0 {
        let mut v___x_717_: u8 = 0;
        v___x_717_ = (leanh::lean_unbox(v_defValue_714_) as u8);
        return v___x_717_;
    } else {
        let mut v_val_718_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_718_ = leanh::lean_ctor_get(v___x_716_, 0);
        leanh::lean_inc(v_val_718_);
        leanh::lean_dec_ref_known(v___x_716_, 1);
        if leanh::lean_obj_tag(v_val_718_) == 1 {
            let mut v_v_719_: u8 = 0;
            v_v_719_ = leanh::lean_ctor_get_uint8(v_val_718_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_718_, 0);
            return v_v_719_;
        } else {
            let mut v___x_720_: u8 = 0;
            leanh::lean_dec(v_val_718_);
            v___x_720_ = (leanh::lean_unbox(v_defValue_714_) as u8);
            return v___x_720_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__3___boxed(
    mut v_opts_721_: *mut leanh::LeanObject,
    mut v_opt_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__3(v_opts_721_, v_opt_722_);
    leanh::lean_dec_ref(v_opt_722_);
    leanh::lean_dec_ref(v_opts_721_);
    v_r_724_ = leanh::lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__1;
    v___x_729_ = l_Lean_MessageData_ofFormat(v___x_728_);
    return v___x_729_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg(
    mut v_msgData_730_: *mut leanh::LeanObject,
    mut v_macroStack_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_743_: u8 = 0;
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut v_unused_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_734_ = leanh::lean_ctor_get(v___y_732_, 2);
                v___x_735_ = l_Lean_Elab_pp_macroStack;
                v___x_736_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__3(v_options_734_, v___x_735_);
                if v___x_736_ == 0 {
                    leanh::lean_dec(v_macroStack_731_);
                    v___x_737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_737_, 0, v_msgData_730_);
                    return v___x_737_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_731_) == 0 {
                        v___x_738_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_738_, 0, v_msgData_730_);
                        return v___x_738_;
                    } else {
                        v_head_739_ = leanh::lean_ctor_get(v_macroStack_731_, 0);
                        leanh::lean_inc(v_head_739_);
                        v_after_740_ = leanh::lean_ctor_get(v_head_739_, 1);
                        v_isSharedCheck_755_ =
                            (!leanh::lean_is_exclusive(v_head_739_)) as u8;
                        if v_isSharedCheck_755_ == 0 {
                            v_unused_756_ = leanh::lean_ctor_get(v_head_739_, 0);
                            leanh::lean_dec(v_unused_756_);
                            v___x_742_ = v_head_739_;
                            v_isShared_743_ = v_isSharedCheck_755_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_740_);
                            leanh::lean_dec(v_head_739_);
                            v___x_742_ = leanh::lean_box(0);
                            v_isShared_743_ = v_isSharedCheck_755_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_743_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_742_, 7);
                    leanh::lean_ctor_set(v___x_742_, 1, v___x_744_);
                    leanh::lean_ctor_set(v___x_742_, 0, v_msgData_730_);
                    v___x_746_ = v___x_742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_754_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_754_, 0, v_msgData_730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_744_);
                    v___x_746_ = v_reuseFailAlloc_754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_747_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___closed__2);
                v___x_748_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_748_, 0, v___x_746_);
                leanh::lean_ctor_set(v___x_748_, 1, v___x_747_);
                v___x_749_ = l_Lean_MessageData_ofSyntax(v_after_740_);
                v___x_750_ = l_Lean_indentD(v___x_749_);
                v_msgData_751_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_751_, 0, v___x_748_);
                leanh::lean_ctor_set(v_msgData_751_, 1, v___x_750_);
                v___x_752_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2_spec__4(v_msgData_751_, v_macroStack_731_);
                v___x_753_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_753_, 0, v___x_752_);
                return v___x_753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg___boxed(
    mut v_msgData_757_: *mut leanh::LeanObject,
    mut v_macroStack_758_: *mut leanh::LeanObject,
    mut v___y_759_: *mut leanh::LeanObject,
    mut v___y_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_761_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg(v_msgData_757_, v_macroStack_758_, v___y_759_);
    leanh::lean_dec_ref(v___y_759_);
    return v_res_761_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__1(
    mut v_msgData_762_: *mut leanh::LeanObject,
    mut v___y_763_: *mut leanh::LeanObject,
    mut v___y_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
    mut v___y_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = lean_st_ref_get(v___y_766_);
    v_env_769_ = leanh::lean_ctor_get(v___x_768_, 0);
    leanh::lean_inc_ref(v_env_769_);
    leanh::lean_dec(v___x_768_);
    v___x_770_ = lean_st_ref_get(v___y_764_);
    v_mctx_771_ = leanh::lean_ctor_get(v___x_770_, 0);
    leanh::lean_inc_ref(v_mctx_771_);
    leanh::lean_dec(v___x_770_);
    v_lctx_772_ = leanh::lean_ctor_get(v___y_763_, 2);
    v_options_773_ = leanh::lean_ctor_get(v___y_765_, 2);
    leanh::lean_inc_ref(v_options_773_);
    leanh::lean_inc_ref(v_lctx_772_);
    v___x_774_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_774_, 0, v_env_769_);
    leanh::lean_ctor_set(v___x_774_, 1, v_mctx_771_);
    leanh::lean_ctor_set(v___x_774_, 2, v_lctx_772_);
    leanh::lean_ctor_set(v___x_774_, 3, v_options_773_);
    v___x_775_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
    leanh::lean_ctor_set(v___x_775_, 1, v_msgData_762_);
    v___x_776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_776_, 0, v___x_775_);
    return v___x_776_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__1___boxed(
    mut v_msgData_777_: *mut leanh::LeanObject,
    mut v___y_778_: *mut leanh::LeanObject,
    mut v___y_779_: *mut leanh::LeanObject,
    mut v___y_780_: *mut leanh::LeanObject,
    mut v___y_781_: *mut leanh::LeanObject,
    mut v___y_782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__1(v_msgData_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
    leanh::lean_dec(v___y_781_);
    leanh::lean_dec_ref(v___y_780_);
    leanh::lean_dec(v___y_779_);
    leanh::lean_dec_ref(v___y_778_);
    return v_res_783_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1___redArg(
    mut v_msg_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
    mut v___y_787_: *mut leanh::LeanObject,
    mut v___y_788_: *mut leanh::LeanObject,
    mut v___y_789_: *mut leanh::LeanObject,
    mut v___y_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_792_ = leanh::lean_ctor_get(v___y_789_, 5);
                v___x_793_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__1(v_msg_784_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
                v_a_794_ = leanh::lean_ctor_get(v___x_793_, 0);
                leanh::lean_inc(v_a_794_);
                leanh::lean_dec_ref(v___x_793_);
                v_macroStack_795_ = leanh::lean_ctor_get(v___y_785_, 1);
                v___x_796_ = l_Lean_Elab_getBetterRef(v_ref_792_, v_macroStack_795_);
                leanh::lean_inc(v_macroStack_795_);
                v___x_797_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg(v_a_794_, v_macroStack_795_, v___y_789_);
                v_a_798_ = leanh::lean_ctor_get(v___x_797_, 0);
                v_isSharedCheck_806_ = (!leanh::lean_is_exclusive(v___x_797_)) as u8;
                if v_isSharedCheck_806_ == 0 {
                    v___x_800_ = v___x_797_;
                    v_isShared_801_ = v_isSharedCheck_806_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_798_);
                    leanh::lean_dec(v___x_797_);
                    v___x_800_ = leanh::lean_box(0);
                    v_isShared_801_ = v_isSharedCheck_806_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_802_, 0, v___x_796_);
                leanh::lean_ctor_set(v___x_802_, 1, v_a_798_);
                if v_isShared_801_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_800_, 1);
                    leanh::lean_ctor_set(v___x_800_, 0, v___x_802_);
                    v___x_804_ = v___x_800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
                    v___x_804_ = v_reuseFailAlloc_805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1___redArg___boxed(
    mut v_msg_807_: *mut leanh::LeanObject,
    mut v___y_808_: *mut leanh::LeanObject,
    mut v___y_809_: *mut leanh::LeanObject,
    mut v___y_810_: *mut leanh::LeanObject,
    mut v___y_811_: *mut leanh::LeanObject,
    mut v___y_812_: *mut leanh::LeanObject,
    mut v___y_813_: *mut leanh::LeanObject,
    mut v___y_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_815_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1___redArg(v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
    leanh::lean_dec(v___y_813_);
    leanh::lean_dec_ref(v___y_812_);
    leanh::lean_dec(v___y_811_);
    leanh::lean_dec_ref(v___y_810_);
    leanh::lean_dec(v___y_809_);
    leanh::lean_dec_ref(v___y_808_);
    return v_res_815_;
}
pub unsafe fn _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = leanh::lean_box(0);
    v___x_829_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__6;
    v___x_830_ = l_Lean_mkConst(v___x_829_, v___x_828_);
    return v___x_830_;
}
pub unsafe fn _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__7),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__7_once
        ),
        _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__7,
    );
    v___x_832_ = leanh::lean_unsigned_to_nat(2);
    v___x_833_ = lean_mk_empty_array_with_capacity(v___x_832_);
    v___x_834_ = lean_array_push(v___x_833_, v___x_831_);
    return v___x_834_;
}
pub unsafe fn _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_845_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__14;
    v___x_846_ = l_String_toRawSubstring_x27(v___x_845_);
    return v___x_846_;
}
pub unsafe fn _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_871_ = leanh::lean_box(0);
    v___x_872_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__27;
    v___x_873_ = l_Lean_mkConst(v___x_872_, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__28),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__28_once
        ),
        _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__28,
    );
    v___x_875_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8),
        core::ptr::addr_of_mut!(
            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8_once
        ),
        _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8,
    );
    v___x_876_ = lean_array_push(v___x_875_, v___x_874_);
    return v___x_876_;
}
pub unsafe fn _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_883_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__32;
    v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
    return v___x_884_;
}
pub unsafe fn l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit(
    mut v_stx_885_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_886_: *mut leanh::LeanObject,
    mut v_a_887_: *mut leanh::LeanObject,
    mut v_a_888_: *mut leanh::LeanObject,
    mut v_a_889_: *mut leanh::LeanObject,
    mut v_a_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
    mut v_a_892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_901_: u8 = 0;
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v_a_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_954_: u8 = 0;
    let mut v_a_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_959_: u8 = 0;
    let mut v_a_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_963_: u8 = 0;
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_967_: u8 = 0;
    let mut v_reuseFailAlloc_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_969_: u8 = 0;
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_894_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2;
                leanh::lean_inc(v_stx_885_);
                v___x_895_ = l_Lean_Syntax_isOfKind(v_stx_885_, v___x_894_);
                if v___x_895_ == 0 {
                    leanh::lean_dec(v_expectedType_x3f_886_);
                    leanh::lean_dec(v_stx_885_);
                    v___x_896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__0___redArg();
                    return v___x_896_;
                } else {
                    leanh::lean_inc(v_expectedType_x3f_886_);
                    v___x_897_ = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(
                        v_expectedType_x3f_886_,
                        v_a_887_,
                        v_a_888_,
                        v_a_889_,
                        v_a_890_,
                        v_a_891_,
                        v_a_892_,
                    );
                    if leanh::lean_obj_tag(v___x_897_) == 0 {
                        leanh::lean_dec_ref_known(v___x_897_, 1);
                        if leanh::lean_obj_tag(v_expectedType_x3f_886_) == 1 {
                            v_val_898_ = leanh::lean_ctor_get(v_expectedType_x3f_886_, 0);
                            v_isSharedCheck_969_ =
                                (!leanh::lean_is_exclusive(v_expectedType_x3f_886_)) as u8;
                            if v_isSharedCheck_969_ == 0 {
                                v___x_900_ = v_expectedType_x3f_886_;
                                v_isShared_901_ = v_isSharedCheck_969_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_898_);
                                leanh::lean_dec(v_expectedType_x3f_886_);
                                v___x_900_ = leanh::lean_box(0);
                                v_isShared_901_ = v_isSharedCheck_969_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_expectedType_x3f_886_);
                            leanh::lean_dec(v_stx_885_);
                            v___x_970_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__33), core::ptr::addr_of_mut!(l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__33_once), _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__33);
                            v___x_971_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1___redArg(v___x_970_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
                            return v___x_971_;
                        }
                    } else {
                        leanh::lean_dec(v_expectedType_x3f_886_);
                        leanh::lean_dec(v_stx_885_);
                        v_a_972_ = leanh::lean_ctor_get(v___x_897_, 0);
                        v_isSharedCheck_979_ = (!leanh::lean_is_exclusive(v___x_897_)) as u8;
                        if v_isSharedCheck_979_ == 0 {
                            v___x_974_ = v___x_897_;
                            v_isShared_975_ = v_isSharedCheck_979_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_972_);
                            leanh::lean_dec(v___x_897_);
                            v___x_974_ = leanh::lean_box(0);
                            v_isShared_975_ = v_isSharedCheck_979_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_902_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__4;
                v___x_903_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8_once
                    ),
                    _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__8,
                );
                v___x_904_ = lean_array_push(v___x_903_, v_val_898_);
                v___x_905_ = l_Lean_Meta_mkAppM(
                    v___x_902_, v___x_904_, v_a_889_, v_a_890_, v_a_891_, v_a_892_,
                );
                if leanh::lean_obj_tag(v___x_905_) == 0 {
                    v_a_906_ = leanh::lean_ctor_get(v___x_905_, 0);
                    leanh::lean_inc(v_a_906_);
                    leanh::lean_dec_ref_known(v___x_905_, 1);
                    v_ref_907_ = leanh::lean_ctor_get(v_a_891_, 5);
                    v_quotContext_908_ = leanh::lean_ctor_get(v_a_891_, 10);
                    v_currMacroScope_909_ = leanh::lean_ctor_get(v_a_891_, 11);
                    v___x_910_ = leanh::lean_unsigned_to_nat(1);
                    v___x_911_ = l_Lean_Syntax_getArg(v_stx_885_, v___x_910_);
                    leanh::lean_dec(v_stx_885_);
                    v___x_912_ = 0;
                    v___x_913_ = l_Lean_SourceInfo_fromRef(v_ref_907_, v___x_912_);
                    v___x_914_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__13;
                    v___x_915_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__15
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__15_once
                        ),
                        _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__15,
                    );
                    v___x_916_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__16;
                    leanh::lean_inc(v_currMacroScope_909_);
                    leanh::lean_inc(v_quotContext_908_);
                    v___x_917_ =
                        l_Lean_addMacroScope(v_quotContext_908_, v___x_916_, v_currMacroScope_909_);
                    v___x_918_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__20;
                    leanh::lean_inc_n(v___x_913_, 4);
                    v___x_919_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_919_, 0, v___x_913_);
                    leanh::lean_ctor_set(v___x_919_, 1, v___x_915_);
                    leanh::lean_ctor_set(v___x_919_, 2, v___x_917_);
                    leanh::lean_ctor_set(v___x_919_, 3, v___x_918_);
                    v___x_920_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__22;
                    v___x_921_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__24;
                    v___x_922_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__25;
                    v___x_923_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_923_, 0, v___x_913_);
                    leanh::lean_ctor_set(v___x_923_, 1, v___x_922_);
                    v___x_924_ =
                        l_Lean_Syntax_node2(v___x_913_, v___x_921_, v___x_923_, v___x_911_);
                    v___x_925_ = l_Lean_Syntax_node1(v___x_913_, v___x_920_, v___x_924_);
                    v___x_926_ =
                        l_Lean_Syntax_node2(v___x_913_, v___x_914_, v___x_919_, v___x_925_);
                    if v_isShared_901_ == 0 {
                        leanh::lean_ctor_set(v___x_900_, 0, v_a_906_);
                        v___x_928_ = v___x_900_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_968_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_906_);
                        v___x_928_ = v_reuseFailAlloc_968_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_900_);
                    leanh::lean_dec(v_stx_885_);
                    return v___x_905_;
                }
            }
            2 => {
                v___x_929_ = leanh::lean_box(0);
                v___x_930_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_926_, v___x_928_, v___x_895_, v___x_895_, v___x_929_, v_a_887_, v_a_888_,
                    v_a_889_, v_a_890_, v_a_891_, v_a_892_,
                );
                if leanh::lean_obj_tag(v___x_930_) == 0 {
                    v_a_931_ = leanh::lean_ctor_get(v___x_930_, 0);
                    leanh::lean_inc(v_a_931_);
                    leanh::lean_dec_ref_known(v___x_930_, 1);
                    v___x_932_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__29
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__29_once
                        ),
                        _init_l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__29,
                    );
                    v___x_933_ = l_Lean_Meta_mkAppM(
                        v___x_902_, v___x_932_, v_a_889_, v_a_890_, v_a_891_, v_a_892_,
                    );
                    if leanh::lean_obj_tag(v___x_933_) == 0 {
                        v_a_934_ = leanh::lean_ctor_get(v___x_933_, 0);
                        leanh::lean_inc(v_a_934_);
                        leanh::lean_dec_ref_known(v___x_933_, 1);
                        v___x_935_ =
                            l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__31;
                        v___x_936_ = lean_mk_empty_array_with_capacity(v___x_910_);
                        v___x_937_ = lean_array_push(v___x_936_, v_a_931_);
                        v___x_938_ = l_Lean_Meta_mkAppM(
                            v___x_935_, v___x_937_, v_a_889_, v_a_890_, v_a_891_, v_a_892_,
                        );
                        if leanh::lean_obj_tag(v___x_938_) == 0 {
                            v_a_939_ = leanh::lean_ctor_get(v___x_938_, 0);
                            leanh::lean_inc(v_a_939_);
                            leanh::lean_dec_ref_known(v___x_938_, 1);
                            v___x_940_ =
                                l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_unsafe__1(
                                    v_a_934_, v_a_939_, v_a_889_, v_a_890_, v_a_891_, v_a_892_,
                                );
                            if leanh::lean_obj_tag(v___x_940_) == 0 {
                                v_a_941_ = leanh::lean_ctor_get(v___x_940_, 0);
                                v_isSharedCheck_959_ =
                                    (!leanh::lean_is_exclusive(v___x_940_)) as u8;
                                if v_isSharedCheck_959_ == 0 {
                                    v___x_943_ = v___x_940_;
                                    v_isShared_944_ = v_isSharedCheck_959_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_941_);
                                    leanh::lean_dec(v___x_940_);
                                    v___x_943_ = leanh::lean_box(0);
                                    v_isShared_944_ = v_isSharedCheck_959_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_960_ = leanh::lean_ctor_get(v___x_940_, 0);
                                v_isSharedCheck_967_ =
                                    (!leanh::lean_is_exclusive(v___x_940_)) as u8;
                                if v_isSharedCheck_967_ == 0 {
                                    v___x_962_ = v___x_940_;
                                    v_isShared_963_ = v_isSharedCheck_967_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_960_);
                                    leanh::lean_dec(v___x_940_);
                                    v___x_962_ = leanh::lean_box(0);
                                    v_isShared_963_ = v_isSharedCheck_967_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_934_);
                            return v___x_938_;
                        }
                    } else {
                        leanh::lean_dec(v_a_931_);
                        return v___x_933_;
                    }
                } else {
                    return v___x_930_;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_941_) == 0 {
                    leanh::lean_del_object(v___x_943_);
                    v_a_945_ = leanh::lean_ctor_get(v_a_941_, 0);
                    v_isSharedCheck_954_ = (!leanh::lean_is_exclusive(v_a_941_)) as u8;
                    if v_isSharedCheck_954_ == 0 {
                        v___x_947_ = v_a_941_;
                        v_isShared_948_ = v_isSharedCheck_954_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_945_);
                        leanh::lean_dec(v_a_941_);
                        v___x_947_ = leanh::lean_box(0);
                        v_isShared_948_ = v_isSharedCheck_954_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_955_ = leanh::lean_ctor_get(v_a_941_, 0);
                    leanh::lean_inc(v_a_955_);
                    leanh::lean_dec_ref_known(v_a_941_, 1);
                    if v_isShared_944_ == 0 {
                        leanh::lean_ctor_set(v___x_943_, 0, v_a_955_);
                        v___x_957_ = v___x_943_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_958_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_955_);
                        v___x_957_ = v_reuseFailAlloc_958_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_948_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_947_, 3);
                    v___x_950_ = v___x_947_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_945_);
                    v___x_950_ = v_reuseFailAlloc_953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_951_ = l_Lean_MessageData_ofFormat(v___x_950_);
                v___x_952_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1___redArg(v___x_951_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
                return v___x_952_;
            }
            6 => {
                return v___x_957_;
            }
            7 => {
                if v_isShared_963_ == 0 {
                    v___x_965_ = v___x_962_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
                    v___x_965_ = v_reuseFailAlloc_966_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_965_;
            }
            9 => {
                if v_isShared_975_ == 0 {
                    v___x_977_ = v___x_974_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_978_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
                    v___x_977_ = v_reuseFailAlloc_978_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___boxed(
    mut v_stx_980_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_981_: *mut leanh::LeanObject,
    mut v_a_982_: *mut leanh::LeanObject,
    mut v_a_983_: *mut leanh::LeanObject,
    mut v_a_984_: *mut leanh::LeanObject,
    mut v_a_985_: *mut leanh::LeanObject,
    mut v_a_986_: *mut leanh::LeanObject,
    mut v_a_987_: *mut leanh::LeanObject,
    mut v_a_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_989_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit(
        v_stx_980_,
        v_expectedType_x3f_981_,
        v_a_982_,
        v_a_983_,
        v_a_984_,
        v_a_985_,
        v_a_986_,
        v_a_987_,
    );
    leanh::lean_dec(v_a_987_);
    leanh::lean_dec_ref(v_a_986_);
    leanh::lean_dec(v_a_985_);
    leanh::lean_dec_ref(v_a_984_);
    leanh::lean_dec(v_a_983_);
    leanh::lean_dec_ref(v_a_982_);
    return v_res_989_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1(
    mut v_00_u03b1_990_: *mut leanh::LeanObject,
    mut v_msg_991_: *mut leanh::LeanObject,
    mut v___y_992_: *mut leanh::LeanObject,
    mut v___y_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
    mut v___y_996_: *mut leanh::LeanObject,
    mut v___y_997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1___redArg(v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
    return v___x_999_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1___boxed(
    mut v_00_u03b1_1000_: *mut leanh::LeanObject,
    mut v_msg_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ =
        l_Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1(
            v_00_u03b1_1000_,
            v_msg_1001_,
            v___y_1002_,
            v___y_1003_,
            v___y_1004_,
            v___y_1005_,
            v___y_1006_,
            v___y_1007_,
        );
    leanh::lean_dec(v___y_1007_);
    leanh::lean_dec_ref(v___y_1006_);
    leanh::lean_dec(v___y_1005_);
    leanh::lean_dec_ref(v___y_1004_);
    leanh::lean_dec(v___y_1003_);
    leanh::lean_dec_ref(v___y_1002_);
    return v_res_1009_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2(
    mut v_msgData_1010_: *mut leanh::LeanObject,
    mut v_macroStack_1011_: *mut leanh::LeanObject,
    mut v___y_1012_: *mut leanh::LeanObject,
    mut v___y_1013_: *mut leanh::LeanObject,
    mut v___y_1014_: *mut leanh::LeanObject,
    mut v___y_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
    mut v___y_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___redArg(v_msgData_1010_, v_macroStack_1011_, v___y_1016_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2___boxed(
    mut v_msgData_1020_: *mut leanh::LeanObject,
    mut v_macroStack_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
    mut v___y_1023_: *mut leanh::LeanObject,
    mut v___y_1024_: *mut leanh::LeanObject,
    mut v___y_1025_: *mut leanh::LeanObject,
    mut v___y_1026_: *mut leanh::LeanObject,
    mut v___y_1027_: *mut leanh::LeanObject,
    mut v___y_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit_spec__1_spec__2(v_msgData_1020_, v_macroStack_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
    leanh::lean_dec(v___y_1027_);
    leanh::lean_dec_ref(v___y_1026_);
    leanh::lean_dec(v___y_1025_);
    leanh::lean_dec_ref(v___y_1024_);
    leanh::lean_dec(v___y_1023_);
    leanh::lean_dec_ref(v___y_1022_);
    return v_res_1029_;
}
pub unsafe fn l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1()
-> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_1059_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___closed__2;
    v___x_1060_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___closed__10;
    v___x_1061_ = leanh::lean_alloc_closure(
        l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_1062_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1058_,
        v___x_1059_,
        v___x_1060_,
        v___x_1061_,
    );
    return v___x_1062_;
}
pub unsafe fn l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1___boxed(
    mut v_a_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1064_ = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1();
    return v_res_1064_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_VerLit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Version(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_DSL_instToExprSemVerCore = _init_l_Lake_DSL_instToExprSemVerCore();
    leanh::lean_mark_persistent(l_Lake_DSL_instToExprSemVerCore);
    l_Lake_DSL_instToExprStdVer = _init_l_Lake_DSL_instToExprStdVer();
    leanh::lean_mark_persistent(l_Lake_DSL_instToExprStdVer);
    res = l___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit___regBuiltin___private_Lake_DSL_VerLit_0__Lake_DSL_elabVerLit__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_VerLit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_VerLit(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Version(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Eval(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_VerLit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_VerLit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_VerLit(builtin);
}