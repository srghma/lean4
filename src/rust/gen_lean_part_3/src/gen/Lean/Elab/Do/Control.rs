// Lean compiler output
// Module: Lean.Elab.Do.Control
// Imports: Lean.Meta.ProdN Lean.Elab.Do.Basic Init.Control.Do
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_infer_type, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::l_Lean_Syntax_getId;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Lean_NameSet_contains;
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_ContInfo_toContInfoRefImpl,
    l_Lean_Elab_Do_bindMutVarsFromTuple, l_Lean_Elab_Do_getBreakCont___redArg,
    l_Lean_Elab_Do_getContinueCont___redArg, l_Lean_Elab_Do_getReturnCont___boxed,
    l_Lean_Elab_Do_getReturnCont___redArg, l_Lean_Elab_Do_mkFreshResultType___redArg,
    l_Lean_Elab_Do_mkMonadApp, l_Lean_Elab_Do_withDeadCode___boxed,
    runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_addTermInfo_x27, l_Lean_Elab_Term_mkInstMVar,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_fvarId_x21, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_toExpr, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAppM;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_getFVarFromUserName,
    l_Lean_Meta_getLocalDeclFromUserName, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::ProdN::{
    initialize_Lean_Meta_ProdN, l_Lean_Meta_mkProdMkN, l_Lean_Meta_mkProdN,
    runtime_initialize_Lean_Meta_ProdN,
};
pub static l_Lean_Elab_Do_ControlStack_unStM___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 1,
        m_data: [206, 177, 0],
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_unStM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_unStM___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_unStM___closed__0_value)
                as *mut leanh::LeanObject,
            988715873908496486 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_unStM___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_unStM___closed__2_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 116, 97, 107, 101, 32, 97, 112, 97, 114,
            116, 32, 0,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_unStM___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_unStM___closed__4_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [32, 97, 115, 32, 97, 32, 96, 0],
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_unStM___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_unStM___closed__6_value: leanh::LeanStringObject<41> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            96, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 97, 32, 98, 117, 103, 32, 105, 110,
            32, 116, 104, 101, 32, 96, 100, 111, 96, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111,
            114, 46, 0,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_unStM___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_ControlStack_unStM___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0_value:
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
    m_data: [98, 97, 115, 101, 0],
};
static mut l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_base___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Do_ControlStack_base___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Do_ControlStack_base___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_base___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_base___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Do_ControlStack_base___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Do_ControlStack_base___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_base___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_base___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Do_ControlStack_base___lam__2 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Do_ControlStack_base___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_base___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 114, 111, 100, 0]};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__0_value) as *mut leanh::LeanObject,15289851429949568889 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0_value:
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
    m_data: [83, 116, 97, 116, 101, 84, 32, 0],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2_value:
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
    m_data: [32, 111, 118, 101, 114, 32, 0],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [112, 0],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
        9720699510028671266 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        83, 116, 97, 116, 101, 32, 116, 117, 112, 108, 101, 32, 116, 121, 112, 101, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2_value:
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
    m_data: [44, 32, 103, 111, 116, 32, 0],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 97, 32, 98, 117, 103, 32, 105, 110, 32, 116,
        104, 101, 32, 96, 100, 111, 96, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0_value:
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
    m_data: [83, 116, 97, 116, 101, 84, 0],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__0_value)
            as *mut leanh::LeanObject,
        15071692578205770878 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__0_value) as *mut leanh::LeanObject,18184376426117065311 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0_value:
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
    m_data: [79, 112, 116, 105, 111, 110, 84, 0],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value:
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
    m_data: [114, 117, 110, 0],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        676213555373846428 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        2246790666882826550 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0_value:
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
        79, 112, 116, 105, 111, 110, 84, 32, 111, 118, 101, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [114, 0],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__0_value)
            as *mut leanh::LeanObject,
        2981963283782553289 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2_value:
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
    m_data: [85, 110, 105, 116, 0],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__2_value)
            as *mut leanh::LeanObject,
        9833841078580172006 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [101, 0],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__0_value)
            as *mut leanh::LeanObject,
        18388690793488095770 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [69, 120, 99, 101, 112, 116, 0]};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__0_value) as *mut leanh::LeanObject,15197845462264082926 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [69, 120, 99, 101, 112, 116, 84, 32, 40, 0],
};
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2_value:
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
    m_data: [41, 32, 111, 118, 101, 114, 32, 0],
};
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0_value:
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
    m_data: [69, 120, 99, 101, 112, 116, 84, 0],
};
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__0_value)
            as *mut leanh::LeanObject,
        8286592149339036670 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        6061665049064603500 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value:
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
    m_data: [69, 97, 114, 108, 121, 82, 101, 116, 117, 114, 110, 84, 0],
};
static mut l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value)
            as *mut leanh::LeanObject,
        17475412649409547729 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [69, 97, 114, 108, 121, 82, 101, 116, 117, 114, 110, 0],
};
static mut l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value:
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
    m_data: [114, 117, 110, 75, 0],
};
static mut l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__2_value)
            as *mut leanh::LeanObject,
        7067080356658014851 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value)
            as *mut leanh::LeanObject,
        12010455625581734774 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Do_getReturnCont___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        96, 98, 114, 101, 97, 107, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 110, 101, 115, 116,
        101, 100, 32, 105, 110, 115, 105, 100, 101, 32, 97, 32, 108, 111, 111, 112, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_breakT___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Do_ControlStack_breakT___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_breakT___closed__1_value: leanh::LeanStringObject<7> =
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
        m_data: [66, 114, 101, 97, 107, 84, 0],
    };
static mut l_Lean_Elab_Do_ControlStack_breakT___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_breakT___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__1_value)
                as *mut leanh::LeanObject,
            7003189271677487346 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_breakT___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_breakT___closed__3_value: leanh::LeanStringObject<6> =
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
        m_data: [66, 114, 101, 97, 107, 0],
    };
static mut l_Lean_Elab_Do_ControlStack_breakT___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_breakT___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__3_value)
                as *mut leanh::LeanObject,
            10906666425700568089 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_ControlStack_breakT___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value)
                as *mut leanh::LeanObject,
            2052082663577137876 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_breakT___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        96, 99, 111, 110, 116, 105, 110, 117, 101, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32,
        110, 101, 115, 116, 101, 100, 32, 105, 110, 115, 105, 100, 101, 32, 97, 32, 108, 111, 111,
        112, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_continueT___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Do_ControlStack_continueT___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_continueT___closed__1_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [67, 111, 110, 116, 105, 110, 117, 101, 84, 0],
};
static mut l_Lean_Elab_Do_ControlStack_continueT___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_continueT___closed__2_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__1_value)
            as *mut leanh::LeanObject,
        5041789405110779990 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_continueT___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_continueT___closed__3_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [67, 111, 110, 116, 105, 110, 117, 101, 0],
};
static mut l_Lean_Elab_Do_ControlStack_continueT___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_continueT___closed__4_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__3_value)
            as *mut leanh::LeanObject,
        12743584413723006022 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_ControlStack_continueT___closed__4_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__3_value)
            as *mut leanh::LeanObject,
        12178525747063610487 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_continueT___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value:
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
    m_data: [77, 111, 110, 97, 100, 0],
};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value
        ) as *mut leanh::LeanObject,
        15714375376425966273 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 32, 0]};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [46, 32, 0]};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 0]};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_ControlStack_mkBreak___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [98, 114, 101, 97, 107, 0],
};
static mut l_Lean_Elab_Do_ControlStack_mkBreak___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkBreak___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_breakT___closed__1_value)
            as *mut leanh::LeanObject,
        7003189271677487346 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkBreak___closed__0_value)
                as *mut leanh::LeanObject,
            9460584390193837911 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_mkBreak___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkBreak___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkBreak___closed__2_value: leanh::LeanStringObject<
    18,
> = leanh::LeanStringObject {
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
        98, 114, 101, 97, 107, 32, 114, 101, 115, 117, 108, 116, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_mkBreak___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkBreak___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkContinue___closed__0_value:
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
    m_data: [99, 111, 110, 116, 105, 110, 117, 101, 0],
};
static mut l_Lean_Elab_Do_ControlStack_mkContinue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkContinue___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_continueT___closed__1_value)
            as *mut leanh::LeanObject,
        5041789405110779990 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkContinue___closed__0_value)
            as *mut leanh::LeanObject,
        4042037735842820704 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_mkContinue___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkContinue___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkContinue___closed__2_value:
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
        99, 111, 110, 116, 105, 110, 117, 101, 32, 114, 101, 115, 117, 108, 116, 32, 116, 121, 112,
        101, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_mkContinue___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkContinue___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkReturn___closed__0_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 1,
    m_data: [206, 180, 0],
};
static mut l_Lean_Elab_Do_ControlStack_mkReturn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkReturn___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__0_value)
                as *mut leanh::LeanObject,
            902760705707816722 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_mkReturn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkReturn___closed__2_value: leanh::LeanStringObject<
    25,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        101, 97, 114, 108, 121, 32, 114, 101, 116, 117, 114, 110, 32, 114, 101, 115, 117, 108, 116,
        32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_mkReturn___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkReturn___closed__3_value: leanh::LeanStringObject<
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
    m_data: [114, 101, 116, 117, 114, 110, 0],
};
static mut l_Lean_Elab_Do_ControlStack_mkReturn___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__0_value)
            as *mut leanh::LeanObject,
        17475412649409547729 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__3_value)
                as *mut leanh::LeanObject,
            14085997187276568880 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_mkReturn___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkReturn___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__0_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [65, 112, 112, 108, 105, 99, 97, 116, 105, 118, 101, 0],
};
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__1_value: leanh::LeanStringObject<7> =
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
        m_data: [116, 111, 80, 117, 114, 101, 0],
    };
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__0_value)
                as *mut leanh::LeanObject,
            8402453304082830817 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__1_value)
                as *mut leanh::LeanObject,
            7692708674247216094 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__3_value: leanh::LeanStringObject<
    14,
> = leanh::LeanStringObject {
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
        116, 111, 65, 112, 112, 108, 105, 99, 97, 116, 105, 118, 101, 0,
    ],
};
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__0_value
            ) as *mut leanh::LeanObject,
            15714375376425966273 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__3_value)
                as *mut leanh::LeanObject,
            3063341668206363811 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__5_value: leanh::LeanStringObject<5> =
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
        m_data: [80, 117, 114, 101, 0],
    };
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__6_value: leanh::LeanStringObject<5> =
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
        m_data: [112, 117, 114, 101, 0],
    };
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__5_value)
                as *mut leanh::LeanObject,
            6146206128508995449 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__6_value)
                as *mut leanh::LeanObject,
            76013442081319628 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_ControlStack_mkPure___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlStack_mkPure___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_ControlLifter_ofCont___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Elab_Do_ControlLifter_ofCont___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_ControlLifter_ofCont___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(
    mut v_msgData_2714_: *mut leanh::LeanObject,
    mut v___y_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = lean_st_ref_get(v___y_2718_);
    v_env_2721_ = leanh::lean_ctor_get(v___x_2720_, 0);
    leanh::lean_inc_ref(v_env_2721_);
    leanh::lean_dec(v___x_2720_);
    v___x_2722_ = lean_st_ref_get(v___y_2716_);
    v_mctx_2723_ = leanh::lean_ctor_get(v___x_2722_, 0);
    leanh::lean_inc_ref(v_mctx_2723_);
    leanh::lean_dec(v___x_2722_);
    v_lctx_2724_ = leanh::lean_ctor_get(v___y_2715_, 2);
    v_options_2725_ = leanh::lean_ctor_get(v___y_2717_, 2);
    leanh::lean_inc_ref(v_options_2725_);
    leanh::lean_inc_ref(v_lctx_2724_);
    v___x_2726_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2726_, 0, v_env_2721_);
    leanh::lean_ctor_set(v___x_2726_, 1, v_mctx_2723_);
    leanh::lean_ctor_set(v___x_2726_, 2, v_lctx_2724_);
    leanh::lean_ctor_set(v___x_2726_, 3, v_options_2725_);
    v___x_2727_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2727_, 0, v___x_2726_);
    leanh::lean_ctor_set(v___x_2727_, 1, v_msgData_2714_);
    v___x_2728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2728_, 0, v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0___boxed(
    mut v_msgData_2729_: *mut leanh::LeanObject,
    mut v___y_2730_: *mut leanh::LeanObject,
    mut v___y_2731_: *mut leanh::LeanObject,
    mut v___y_2732_: *mut leanh::LeanObject,
    mut v___y_2733_: *mut leanh::LeanObject,
    mut v___y_2734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msgData_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
    leanh::lean_dec(v___y_2733_);
    leanh::lean_dec_ref(v___y_2732_);
    leanh::lean_dec(v___y_2731_);
    leanh::lean_dec_ref(v___y_2730_);
    return v_res_2735_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
    mut v_msg_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v___y_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2742_ = leanh::lean_ctor_get(v___y_2739_, 5);
                v___x_2743_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0_spec__0(v_msg_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
                v_a_2744_ = leanh::lean_ctor_get(v___x_2743_, 0);
                v_isSharedCheck_2752_ = (!leanh::lean_is_exclusive(v___x_2743_)) as u8;
                if v_isSharedCheck_2752_ == 0 {
                    v___x_2746_ = v___x_2743_;
                    v_isShared_2747_ = v_isSharedCheck_2752_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2744_);
                    leanh::lean_dec(v___x_2743_);
                    v___x_2746_ = leanh::lean_box(0);
                    v_isShared_2747_ = v_isSharedCheck_2752_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2742_);
                v___x_2748_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2748_, 0, v_ref_2742_);
                leanh::lean_ctor_set(v___x_2748_, 1, v_a_2744_);
                if v_isShared_2747_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2746_, 1);
                    leanh::lean_ctor_set(v___x_2746_, 0, v___x_2748_);
                    v___x_2750_ = v___x_2746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
                    v___x_2750_ = v_reuseFailAlloc_2751_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg___boxed(
    mut v_msg_2753_: *mut leanh::LeanObject,
    mut v___y_2754_: *mut leanh::LeanObject,
    mut v___y_2755_: *mut leanh::LeanObject,
    mut v___y_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
        v_msg_2753_,
        v___y_2754_,
        v___y_2755_,
        v___y_2756_,
        v___y_2757_,
    );
    leanh::lean_dec(v___y_2757_);
    leanh::lean_dec_ref(v___y_2756_);
    leanh::lean_dec(v___y_2755_);
    leanh::lean_dec_ref(v___y_2754_);
    return v_res_2759_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = l_Lean_Elab_Do_ControlStack_unStM___closed__2;
    v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = l_Lean_Elab_Do_ControlStack_unStM___closed__4;
    v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
    return v___x_2768_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = l_Lean_Elab_Do_ControlStack_unStM___closed__6;
    v___x_2771_ = l_Lean_stringToMessageData(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_unStM(
    mut v_m_2772_: *mut leanh::LeanObject,
    mut v_stM_u03b1_2773_: *mut leanh::LeanObject,
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_a_2775_: *mut leanh::LeanObject,
    mut v_a_2776_: *mut leanh::LeanObject,
    mut v_a_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stM_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: u8 = 0;
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2812_: u8 = 0;
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_a_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2782_ = l_Lean_Elab_Do_ControlStack_unStM___closed__1;
                v___x_2783_ = 0;
                v___x_2784_ = l_Lean_Elab_Do_mkFreshResultType___redArg(
                    v___x_2782_,
                    v___x_2783_,
                    v_a_2774_,
                    v_a_2777_,
                    v_a_2778_,
                    v_a_2779_,
                    v_a_2780_,
                );
                if leanh::lean_obj_tag(v___x_2784_) == 0 {
                    v_a_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    leanh::lean_inc_n(v_a_2785_, 2);
                    leanh::lean_dec_ref_known(v___x_2784_, 1);
                    v_stM_2786_ = leanh::lean_ctor_get(v_m_2772_, 2);
                    leanh::lean_inc_ref(v_stM_2786_);
                    leanh::lean_dec_ref(v_m_2772_);
                    leanh::lean_inc(v_a_2780_);
                    leanh::lean_inc_ref(v_a_2779_);
                    leanh::lean_inc(v_a_2778_);
                    leanh::lean_inc_ref(v_a_2777_);
                    leanh::lean_inc(v_a_2776_);
                    leanh::lean_inc_ref(v_a_2775_);
                    leanh::lean_inc_ref(v_a_2774_);
                    v___x_2787_ = leanh::lean_apply_9(
                        v_stM_2786_,
                        v_a_2785_,
                        v_a_2774_,
                        v_a_2775_,
                        v_a_2776_,
                        v_a_2777_,
                        v_a_2778_,
                        v_a_2779_,
                        v_a_2780_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2787_) == 0 {
                        v_a_2788_ = leanh::lean_ctor_get(v___x_2787_, 0);
                        leanh::lean_inc_n(v_a_2788_, 2);
                        leanh::lean_dec_ref_known(v___x_2787_, 1);
                        leanh::lean_inc_ref(v_stM_u03b1_2773_);
                        v___x_2789_ = l_Lean_Meta_isExprDefEq(
                            v_stM_u03b1_2773_,
                            v_a_2788_,
                            v_a_2777_,
                            v_a_2778_,
                            v_a_2779_,
                            v_a_2780_,
                        );
                        if leanh::lean_obj_tag(v___x_2789_) == 0 {
                            v_a_2790_ = leanh::lean_ctor_get(v___x_2789_, 0);
                            v_isSharedCheck_2816_ =
                                (!leanh::lean_is_exclusive(v___x_2789_)) as u8;
                            if v_isSharedCheck_2816_ == 0 {
                                v___x_2792_ = v___x_2789_;
                                v_isShared_2793_ = v_isSharedCheck_2816_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2790_);
                                leanh::lean_dec(v___x_2789_);
                                v___x_2792_ = leanh::lean_box(0);
                                v_isShared_2793_ = v_isSharedCheck_2816_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2788_);
                            leanh::lean_dec(v_a_2785_);
                            leanh::lean_dec_ref(v_stM_u03b1_2773_);
                            v_a_2817_ = leanh::lean_ctor_get(v___x_2789_, 0);
                            v_isSharedCheck_2824_ =
                                (!leanh::lean_is_exclusive(v___x_2789_)) as u8;
                            if v_isSharedCheck_2824_ == 0 {
                                v___x_2819_ = v___x_2789_;
                                v_isShared_2820_ = v_isSharedCheck_2824_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2817_);
                                leanh::lean_dec(v___x_2789_);
                                v___x_2819_ = leanh::lean_box(0);
                                v_isShared_2820_ = v_isSharedCheck_2824_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2785_);
                        leanh::lean_dec_ref(v_stM_u03b1_2773_);
                        return v___x_2787_;
                    }
                } else {
                    leanh::lean_dec_ref(v_stM_u03b1_2773_);
                    leanh::lean_dec_ref(v_m_2772_);
                    return v___x_2784_;
                }
            }
            1 => {
                v___x_2794_ = (leanh::lean_unbox(v_a_2790_) as u8);
                leanh::lean_dec(v_a_2790_);
                if v___x_2794_ == 0 {
                    leanh::lean_del_object(v___x_2792_);
                    leanh::lean_dec(v_a_2785_);
                    v___x_2795_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_unStM___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_unStM___closed__3_once),
                        _init_l_Lean_Elab_Do_ControlStack_unStM___closed__3,
                    );
                    v___x_2796_ = l_Lean_MessageData_ofExpr(v_stM_u03b1_2773_);
                    v___x_2797_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2797_, 0, v___x_2795_);
                    leanh::lean_ctor_set(v___x_2797_, 1, v___x_2796_);
                    v___x_2798_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_unStM___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_unStM___closed__5_once),
                        _init_l_Lean_Elab_Do_ControlStack_unStM___closed__5,
                    );
                    v___x_2799_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2799_, 0, v___x_2797_);
                    leanh::lean_ctor_set(v___x_2799_, 1, v___x_2798_);
                    v___x_2800_ = l_Lean_MessageData_ofExpr(v_a_2788_);
                    v___x_2801_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2801_, 0, v___x_2799_);
                    leanh::lean_ctor_set(v___x_2801_, 1, v___x_2800_);
                    v___x_2802_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_unStM___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_unStM___closed__7_once),
                        _init_l_Lean_Elab_Do_ControlStack_unStM___closed__7,
                    );
                    v___x_2803_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2803_, 0, v___x_2801_);
                    leanh::lean_ctor_set(v___x_2803_, 1, v___x_2802_);
                    v___x_2804_ =
                        l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
                            v___x_2803_,
                            v_a_2777_,
                            v_a_2778_,
                            v_a_2779_,
                            v_a_2780_,
                        );
                    v_a_2805_ = leanh::lean_ctor_get(v___x_2804_, 0);
                    v_isSharedCheck_2812_ = (!leanh::lean_is_exclusive(v___x_2804_)) as u8;
                    if v_isSharedCheck_2812_ == 0 {
                        v___x_2807_ = v___x_2804_;
                        v_isShared_2808_ = v_isSharedCheck_2812_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2805_);
                        leanh::lean_dec(v___x_2804_);
                        v___x_2807_ = leanh::lean_box(0);
                        v_isShared_2808_ = v_isSharedCheck_2812_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2788_);
                    leanh::lean_dec_ref(v_stM_u03b1_2773_);
                    if v_isShared_2793_ == 0 {
                        leanh::lean_ctor_set(v___x_2792_, 0, v_a_2785_);
                        v___x_2814_ = v___x_2792_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2815_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2785_);
                        v___x_2814_ = v_reuseFailAlloc_2815_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2808_ == 0 {
                    v___x_2810_ = v___x_2807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
                    v___x_2810_ = v_reuseFailAlloc_2811_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2810_;
            }
            4 => {
                return v___x_2814_;
            }
            5 => {
                if v_isShared_2820_ == 0 {
                    v___x_2822_ = v___x_2819_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2823_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
                    v___x_2822_ = v_reuseFailAlloc_2823_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_unStM___boxed(
    mut v_m_2825_: *mut leanh::LeanObject,
    mut v_stM_u03b1_2826_: *mut leanh::LeanObject,
    mut v_a_2827_: *mut leanh::LeanObject,
    mut v_a_2828_: *mut leanh::LeanObject,
    mut v_a_2829_: *mut leanh::LeanObject,
    mut v_a_2830_: *mut leanh::LeanObject,
    mut v_a_2831_: *mut leanh::LeanObject,
    mut v_a_2832_: *mut leanh::LeanObject,
    mut v_a_2833_: *mut leanh::LeanObject,
    mut v_a_2834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2835_ = l_Lean_Elab_Do_ControlStack_unStM(
        v_m_2825_,
        v_stM_u03b1_2826_,
        v_a_2827_,
        v_a_2828_,
        v_a_2829_,
        v_a_2830_,
        v_a_2831_,
        v_a_2832_,
        v_a_2833_,
    );
    leanh::lean_dec(v_a_2833_);
    leanh::lean_dec_ref(v_a_2832_);
    leanh::lean_dec(v_a_2831_);
    leanh::lean_dec_ref(v_a_2830_);
    leanh::lean_dec(v_a_2829_);
    leanh::lean_dec_ref(v_a_2828_);
    leanh::lean_dec_ref(v_a_2827_);
    return v_res_2835_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(
    mut v_00_u03b1_2836_: *mut leanh::LeanObject,
    mut v_msg_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
    mut v___y_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2846_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
        v_msg_2837_,
        v___y_2841_,
        v___y_2842_,
        v___y_2843_,
        v___y_2844_,
    );
    return v___x_2846_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___boxed(
    mut v_00_u03b1_2847_: *mut leanh::LeanObject,
    mut v_msg_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
    mut v___y_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2857_ = l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0(
        v_00_u03b1_2847_,
        v_msg_2848_,
        v___y_2849_,
        v___y_2850_,
        v___y_2851_,
        v___y_2852_,
        v___y_2853_,
        v___y_2854_,
        v___y_2855_,
    );
    leanh::lean_dec(v___y_2855_);
    leanh::lean_dec_ref(v___y_2854_);
    leanh::lean_dec(v___y_2853_);
    leanh::lean_dec_ref(v___y_2852_);
    leanh::lean_dec(v___y_2851_);
    leanh::lean_dec_ref(v___y_2850_);
    leanh::lean_dec_ref(v___y_2849_);
    return v_res_2857_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base___lam__0(
    mut v_dec_2858_: *mut leanh::LeanObject,
    mut v___y_2859_: *mut leanh::LeanObject,
    mut v___y_2860_: *mut leanh::LeanObject,
    mut v___y_2861_: *mut leanh::LeanObject,
    mut v___y_2862_: *mut leanh::LeanObject,
    mut v___y_2863_: *mut leanh::LeanObject,
    mut v___y_2864_: *mut leanh::LeanObject,
    mut v___y_2865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2867_, 0, v_dec_2858_);
    return v___x_2867_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base___lam__0___boxed(
    mut v_dec_2868_: *mut leanh::LeanObject,
    mut v___y_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2877_ = l_Lean_Elab_Do_ControlStack_base___lam__0(
        v_dec_2868_,
        v___y_2869_,
        v___y_2870_,
        v___y_2871_,
        v___y_2872_,
        v___y_2873_,
        v___y_2874_,
        v___y_2875_,
    );
    leanh::lean_dec(v___y_2875_);
    leanh::lean_dec_ref(v___y_2874_);
    leanh::lean_dec(v___y_2873_);
    leanh::lean_dec_ref(v___y_2872_);
    leanh::lean_dec(v___y_2871_);
    leanh::lean_dec_ref(v___y_2870_);
    leanh::lean_dec_ref(v___y_2869_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base___lam__1(
    mut v_00_u03b1_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
    mut v___y_2881_: *mut leanh::LeanObject,
    mut v___y_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2887_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2887_, 0, v_00_u03b1_2878_);
    return v___x_2887_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base___lam__1___boxed(
    mut v_00_u03b1_2888_: *mut leanh::LeanObject,
    mut v___y_2889_: *mut leanh::LeanObject,
    mut v___y_2890_: *mut leanh::LeanObject,
    mut v___y_2891_: *mut leanh::LeanObject,
    mut v___y_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
    mut v___y_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2897_ = l_Lean_Elab_Do_ControlStack_base___lam__1(
        v_00_u03b1_2888_,
        v___y_2889_,
        v___y_2890_,
        v___y_2891_,
        v___y_2892_,
        v___y_2893_,
        v___y_2894_,
        v___y_2895_,
    );
    leanh::lean_dec(v___y_2895_);
    leanh::lean_dec_ref(v___y_2894_);
    leanh::lean_dec(v___y_2893_);
    leanh::lean_dec_ref(v___y_2892_);
    leanh::lean_dec(v___y_2891_);
    leanh::lean_dec_ref(v___y_2890_);
    leanh::lean_dec_ref(v___y_2889_);
    return v_res_2897_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2901_ = l_Lean_Elab_Do_ControlStack_base___lam__2___closed__1;
    v___x_2902_ = l_Lean_MessageData_ofFormat(v___x_2901_);
    return v___x_2902_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base___lam__2(
    mut v_x_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2_once),
        _init_l_Lean_Elab_Do_ControlStack_base___lam__2___closed__2,
    );
    return v___x_2904_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base___lam__3(
    mut v_m_2905_: *mut leanh::LeanObject,
    mut v___y_2906_: *mut leanh::LeanObject,
    mut v___y_2907_: *mut leanh::LeanObject,
    mut v___y_2908_: *mut leanh::LeanObject,
    mut v___y_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2914_, 0, v_m_2905_);
    return v___x_2914_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base___lam__3___boxed(
    mut v_m_2915_: *mut leanh::LeanObject,
    mut v___y_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
    mut v___y_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2924_ = l_Lean_Elab_Do_ControlStack_base___lam__3(
        v_m_2915_,
        v___y_2916_,
        v___y_2917_,
        v___y_2918_,
        v___y_2919_,
        v___y_2920_,
        v___y_2921_,
        v___y_2922_,
    );
    leanh::lean_dec(v___y_2922_);
    leanh::lean_dec_ref(v___y_2921_);
    leanh::lean_dec(v___y_2920_);
    leanh::lean_dec_ref(v___y_2919_);
    leanh::lean_dec(v___y_2918_);
    leanh::lean_dec_ref(v___y_2917_);
    leanh::lean_dec_ref(v___y_2916_);
    return v_res_2924_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_base(
    mut v_mi_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_m_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2932_: u8 = 0;
    let mut v___f_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2940_: u8 = 0;
    let mut v_unused_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_m_2929_ = leanh::lean_ctor_get(v_mi_2928_, 0);
                v_isSharedCheck_2940_ = (!leanh::lean_is_exclusive(v_mi_2928_)) as u8;
                if v_isSharedCheck_2940_ == 0 {
                    v_unused_2941_ = leanh::lean_ctor_get(v_mi_2928_, 4);
                    leanh::lean_dec(v_unused_2941_);
                    v_unused_2942_ = leanh::lean_ctor_get(v_mi_2928_, 3);
                    leanh::lean_dec(v_unused_2942_);
                    v_unused_2943_ = leanh::lean_ctor_get(v_mi_2928_, 2);
                    leanh::lean_dec(v_unused_2943_);
                    v_unused_2944_ = leanh::lean_ctor_get(v_mi_2928_, 1);
                    leanh::lean_dec(v_unused_2944_);
                    v___x_2931_ = v_mi_2928_;
                    v_isShared_2932_ = v_isSharedCheck_2940_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_m_2929_);
                    leanh::lean_dec(v_mi_2928_);
                    v___x_2931_ = leanh::lean_box(0);
                    v_isShared_2932_ = v_isSharedCheck_2940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2933_ = l_Lean_Elab_Do_ControlStack_base___closed__0;
                v___f_2934_ = l_Lean_Elab_Do_ControlStack_base___closed__1;
                v___f_2935_ = l_Lean_Elab_Do_ControlStack_base___closed__2;
                v___f_2936_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_base___lam__3___boxed as *mut core::ffi::c_void,
                    9,
                    1,
                );
                leanh::lean_closure_set(v___f_2936_, 0, v_m_2929_);
                if v_isShared_2932_ == 0 {
                    leanh::lean_ctor_set(v___x_2931_, 4, v___f_2933_);
                    leanh::lean_ctor_set(v___x_2931_, 3, v___f_2934_);
                    leanh::lean_ctor_set(v___x_2931_, 2, v___f_2934_);
                    leanh::lean_ctor_set(v___x_2931_, 1, v___f_2936_);
                    leanh::lean_ctor_set(v___x_2931_, 0, v___f_2935_);
                    v___x_2938_ = v___x_2931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2939_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___f_2935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 1, v___f_2936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 2, v___f_2934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 3, v___f_2934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 4, v___f_2933_);
                    v___x_2938_ = v_reuseFailAlloc_2939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(
    mut v_sz_2945_: usize,
    mut v_i_2946_: usize,
    mut v_bs_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2948_: u8 = 0;
    let mut v_v_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: usize = 0;
    let mut v___x_2954_: usize = 0;
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2948_ = lean_usize_dec_lt(v_i_2946_, v_sz_2945_);
                if v___x_2948_ == 0 {
                    return v_bs_2947_;
                } else {
                    v_v_2949_ = lean_array_uget(v_bs_2947_, v_i_2946_);
                    v___x_2950_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2951_ = lean_array_uset(v_bs_2947_, v_i_2946_, v___x_2950_);
                    v___x_2952_ = l_Lean_TSyntax_getId(v_v_2949_);
                    leanh::lean_dec(v_v_2949_);
                    v___x_2953_ = 1usize;
                    v___x_2954_ = lean_usize_add(v_i_2946_, v___x_2953_);
                    v___x_2955_ = lean_array_uset(v_bs_x27_2951_, v_i_2946_, v___x_2952_);
                    v_i_2946_ = v___x_2954_;
                    v_bs_2947_ = v___x_2955_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0___boxed(
    mut v_sz_2957_: *mut leanh::LeanObject,
    mut v_i_2958_: *mut leanh::LeanObject,
    mut v_bs_2959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2960_: usize = 0;
    let mut v_i_boxed_2961_: usize = 0;
    let mut v_res_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2960_ = leanh::lean_unbox_usize(v_sz_2957_);
    leanh::lean_dec(v_sz_2957_);
    v_i_boxed_2961_ = leanh::lean_unbox_usize(v_i_2958_);
    leanh::lean_dec(v_i_2958_);
    v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_boxed_2960_, v_i_boxed_2961_, v_bs_2959_);
    return v_res_2962_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(
    mut v_mutVarIdents_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_2964_: usize = 0;
    let mut v___x_2965_: usize = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_2964_ = lean_array_size(v_mutVarIdents_2963_);
    v___x_2965_ = 0usize;
    v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_2964_, v___x_2965_, v_mutVarIdents_2963_);
    return v___x_2966_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(
    mut v_sz_2967_: usize,
    mut v_i_2968_: usize,
    mut v_bs_2969_: *mut leanh::LeanObject,
    mut v___y_2970_: *mut leanh::LeanObject,
    mut v___y_2971_: *mut leanh::LeanObject,
    mut v___y_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: usize = 0;
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2990_: u8 = 0;
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2975_ = lean_usize_dec_lt(v_i_2968_, v_sz_2967_);
                if v___x_2975_ == 0 {
                    v___x_2976_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2976_, 0, v_bs_2969_);
                    return v___x_2976_;
                } else {
                    v_v_2977_ = lean_array_uget_borrowed(v_bs_2969_, v_i_2968_);
                    leanh::lean_inc(v_v_2977_);
                    v___x_2978_ = l_Lean_Meta_getLocalDeclFromUserName(
                        v_v_2977_,
                        v___y_2970_,
                        v___y_2971_,
                        v___y_2972_,
                        v___y_2973_,
                    );
                    if leanh::lean_obj_tag(v___x_2978_) == 0 {
                        v_a_2979_ = leanh::lean_ctor_get(v___x_2978_, 0);
                        leanh::lean_inc(v_a_2979_);
                        leanh::lean_dec_ref_known(v___x_2978_, 1);
                        v___x_2980_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2981_ = lean_array_uset(v_bs_2969_, v_i_2968_, v___x_2980_);
                        v___x_2982_ = l_Lean_LocalDecl_type(v_a_2979_);
                        leanh::lean_dec(v_a_2979_);
                        v___x_2983_ = 1usize;
                        v___x_2984_ = lean_usize_add(v_i_2968_, v___x_2983_);
                        v___x_2985_ = lean_array_uset(v_bs_x27_2981_, v_i_2968_, v___x_2982_);
                        v_i_2968_ = v___x_2984_;
                        v_bs_2969_ = v___x_2985_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_2969_);
                        v_a_2987_ = leanh::lean_ctor_get(v___x_2978_, 0);
                        v_isSharedCheck_2994_ =
                            (!leanh::lean_is_exclusive(v___x_2978_)) as u8;
                        if v_isSharedCheck_2994_ == 0 {
                            v___x_2989_ = v___x_2978_;
                            v_isShared_2990_ = v_isSharedCheck_2994_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2987_);
                            leanh::lean_dec(v___x_2978_);
                            v___x_2989_ = leanh::lean_box(0);
                            v_isShared_2990_ = v_isSharedCheck_2994_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2990_ == 0 {
                    v___x_2992_ = v___x_2989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg___boxed(
    mut v_sz_2995_: *mut leanh::LeanObject,
    mut v_i_2996_: *mut leanh::LeanObject,
    mut v_bs_2997_: *mut leanh::LeanObject,
    mut v___y_2998_: *mut leanh::LeanObject,
    mut v___y_2999_: *mut leanh::LeanObject,
    mut v___y_3000_: *mut leanh::LeanObject,
    mut v___y_3001_: *mut leanh::LeanObject,
    mut v___y_3002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3003_: usize = 0;
    let mut v_i_boxed_3004_: usize = 0;
    let mut v_res_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3003_ = leanh::lean_unbox_usize(v_sz_2995_);
    leanh::lean_dec(v_sz_2995_);
    v_i_boxed_3004_ = leanh::lean_unbox_usize(v_i_2996_);
    leanh::lean_dec(v_i_2996_);
    v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_boxed_3003_, v_i_boxed_3004_, v_bs_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
    leanh::lean_dec(v___y_3001_);
    leanh::lean_dec_ref(v___y_3000_);
    leanh::lean_dec(v___y_2999_);
    leanh::lean_dec_ref(v___y_2998_);
    return v_res_3005_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(
    mut v_baseMonadInfo_3006_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3007_: *mut leanh::LeanObject,
    mut v_a_3008_: *mut leanh::LeanObject,
    mut v_a_3009_: *mut leanh::LeanObject,
    mut v_a_3010_: *mut leanh::LeanObject,
    mut v_a_3011_: *mut leanh::LeanObject,
    mut v_a_3012_: *mut leanh::LeanObject,
    mut v_a_3013_: *mut leanh::LeanObject,
    mut v_a_3014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3017_: usize = 0;
    let mut v___x_3018_: usize = 0;
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3016_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(v_mutVarIdents_3007_);
                v_sz_3017_ = lean_array_size(v___x_3016_);
                v___x_3018_ = 0usize;
                v___x_3019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_3017_, v___x_3018_, v___x_3016_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
                if leanh::lean_obj_tag(v___x_3019_) == 0 {
                    v_a_3020_ = leanh::lean_ctor_get(v___x_3019_, 0);
                    leanh::lean_inc(v_a_3020_);
                    leanh::lean_dec_ref_known(v___x_3019_, 1);
                    v_u_3021_ = leanh::lean_ctor_get(v_baseMonadInfo_3006_, 1);
                    leanh::lean_inc(v_u_3021_);
                    leanh::lean_dec_ref(v_baseMonadInfo_3006_);
                    v___x_3022_ = l_Lean_Meta_mkProdN(
                        v_a_3020_, v_u_3021_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_,
                    );
                    return v___x_3022_;
                } else {
                    leanh::lean_dec_ref(v_baseMonadInfo_3006_);
                    v_a_3023_ = leanh::lean_ctor_get(v___x_3019_, 0);
                    v_isSharedCheck_3030_ = (!leanh::lean_is_exclusive(v___x_3019_)) as u8;
                    if v_isSharedCheck_3030_ == 0 {
                        v___x_3025_ = v___x_3019_;
                        v_isShared_3026_ = v_isSharedCheck_3030_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3023_);
                        leanh::lean_dec(v___x_3019_);
                        v___x_3025_ = leanh::lean_box(0);
                        v_isShared_3026_ = v_isSharedCheck_3030_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3026_ == 0 {
                    v___x_3028_ = v___x_3025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
                    v___x_3028_ = v_reuseFailAlloc_3029_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3___boxed(
    mut v_baseMonadInfo_3031_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3032_: *mut leanh::LeanObject,
    mut v_a_3033_: *mut leanh::LeanObject,
    mut v_a_3034_: *mut leanh::LeanObject,
    mut v_a_3035_: *mut leanh::LeanObject,
    mut v_a_3036_: *mut leanh::LeanObject,
    mut v_a_3037_: *mut leanh::LeanObject,
    mut v_a_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3041_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(
        v_baseMonadInfo_3031_,
        v_mutVarIdents_3032_,
        v_a_3033_,
        v_a_3034_,
        v_a_3035_,
        v_a_3036_,
        v_a_3037_,
        v_a_3038_,
        v_a_3039_,
    );
    leanh::lean_dec(v_a_3039_);
    leanh::lean_dec_ref(v_a_3038_);
    leanh::lean_dec(v_a_3037_);
    leanh::lean_dec_ref(v_a_3036_);
    leanh::lean_dec(v_a_3035_);
    leanh::lean_dec_ref(v_a_3034_);
    leanh::lean_dec_ref(v_a_3033_);
    return v_res_3041_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(
    mut v_sz_3042_: usize,
    mut v_i_3043_: usize,
    mut v_bs_3044_: *mut leanh::LeanObject,
    mut v___y_3045_: *mut leanh::LeanObject,
    mut v___y_3046_: *mut leanh::LeanObject,
    mut v___y_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_3042_, v_i_3043_, v_bs_3044_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
    return v___x_3053_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___boxed(
    mut v_sz_3054_: *mut leanh::LeanObject,
    mut v_i_3055_: *mut leanh::LeanObject,
    mut v_bs_3056_: *mut leanh::LeanObject,
    mut v___y_3057_: *mut leanh::LeanObject,
    mut v___y_3058_: *mut leanh::LeanObject,
    mut v___y_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
    mut v___y_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
    mut v___y_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3065_: usize = 0;
    let mut v_i_boxed_3066_: usize = 0;
    let mut v_res_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3065_ = leanh::lean_unbox_usize(v_sz_3054_);
    leanh::lean_dec(v_sz_3054_);
    v_i_boxed_3066_ = leanh::lean_unbox_usize(v_i_3055_);
    leanh::lean_dec(v_i_3055_);
    v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0(v_sz_boxed_3065_, v_i_boxed_3066_, v_bs_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
    leanh::lean_dec(v___y_3063_);
    leanh::lean_dec_ref(v___y_3062_);
    leanh::lean_dec(v___y_3061_);
    leanh::lean_dec_ref(v___y_3060_);
    leanh::lean_dec(v___y_3059_);
    leanh::lean_dec_ref(v___y_3058_);
    leanh::lean_dec_ref(v___y_3057_);
    return v_res_3067_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(
    mut v_baseMonadInfo_3071_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3072_: *mut leanh::LeanObject,
    mut v_00_u03b1_3073_: *mut leanh::LeanObject,
    mut v_a_3074_: *mut leanh::LeanObject,
    mut v_a_3075_: *mut leanh::LeanObject,
    mut v_a_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
    mut v_a_3078_: *mut leanh::LeanObject,
    mut v_a_3079_: *mut leanh::LeanObject,
    mut v_a_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3086_: u8 = 0;
    let mut v_u_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_baseMonadInfo_3071_);
                v___x_3082_ =
                    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(
                        v_baseMonadInfo_3071_,
                        v_mutVarIdents_3072_,
                        v_a_3074_,
                        v_a_3075_,
                        v_a_3076_,
                        v_a_3077_,
                        v_a_3078_,
                        v_a_3079_,
                        v_a_3080_,
                    );
                if leanh::lean_obj_tag(v___x_3082_) == 0 {
                    v_a_3083_ = leanh::lean_ctor_get(v___x_3082_, 0);
                    v_isSharedCheck_3097_ = (!leanh::lean_is_exclusive(v___x_3082_)) as u8;
                    if v_isSharedCheck_3097_ == 0 {
                        v___x_3085_ = v___x_3082_;
                        v_isShared_3086_ = v_isSharedCheck_3097_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3083_);
                        leanh::lean_dec(v___x_3082_);
                        v___x_3085_ = leanh::lean_box(0);
                        v_isShared_3086_ = v_isSharedCheck_3097_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_00_u03b1_3073_);
                    leanh::lean_dec_ref(v_baseMonadInfo_3071_);
                    return v___x_3082_;
                }
            }
            1 => {
                v_u_3087_ = leanh::lean_ctor_get(v_baseMonadInfo_3071_, 1);
                leanh::lean_inc_n(v_u_3087_, 2);
                leanh::lean_dec_ref(v_baseMonadInfo_3071_);
                v___x_3088_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___closed__1;
                v___x_3089_ = leanh::lean_box(0);
                v___x_3090_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3090_, 0, v_u_3087_);
                leanh::lean_ctor_set(v___x_3090_, 1, v___x_3089_);
                v___x_3091_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3091_, 0, v_u_3087_);
                leanh::lean_ctor_set(v___x_3091_, 1, v___x_3090_);
                v___x_3092_ = l_Lean_mkConst(v___x_3088_, v___x_3091_);
                v___x_3093_ = l_Lean_mkAppB(v___x_3092_, v_00_u03b1_3073_, v_a_3083_);
                if v_isShared_3086_ == 0 {
                    leanh::lean_ctor_set(v___x_3085_, 0, v___x_3093_);
                    v___x_3095_ = v___x_3085_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
                    v___x_3095_ = v_reuseFailAlloc_3096_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM___boxed(
    mut v_baseMonadInfo_3098_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3099_: *mut leanh::LeanObject,
    mut v_00_u03b1_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
    mut v_a_3102_: *mut leanh::LeanObject,
    mut v_a_3103_: *mut leanh::LeanObject,
    mut v_a_3104_: *mut leanh::LeanObject,
    mut v_a_3105_: *mut leanh::LeanObject,
    mut v_a_3106_: *mut leanh::LeanObject,
    mut v_a_3107_: *mut leanh::LeanObject,
    mut v_a_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3109_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(
        v_baseMonadInfo_3098_,
        v_mutVarIdents_3099_,
        v_00_u03b1_3100_,
        v_a_3101_,
        v_a_3102_,
        v_a_3103_,
        v_a_3104_,
        v_a_3105_,
        v_a_3106_,
        v_a_3107_,
    );
    leanh::lean_dec(v_a_3107_);
    leanh::lean_dec_ref(v_a_3106_);
    leanh::lean_dec(v_a_3105_);
    leanh::lean_dec_ref(v_a_3104_);
    leanh::lean_dec(v_a_3103_);
    leanh::lean_dec_ref(v_a_3102_);
    leanh::lean_dec_ref(v_a_3101_);
    return v_res_3109_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3111_ = l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__0;
    v___x_3112_ = l_Lean_stringToMessageData(v___x_3111_);
    return v___x_3112_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__2;
    v___x_3115_ = l_Lean_stringToMessageData(v___x_3114_);
    return v___x_3115_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__0(
    mut v_base_3116_: *mut leanh::LeanObject,
    mut v_00_u03c3_3117_: *mut leanh::LeanObject,
    mut v_x_3118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_description_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_description_3119_ = leanh::lean_ctor_get(v_base_3116_, 0);
    leanh::lean_inc_ref(v_description_3119_);
    leanh::lean_dec_ref(v_base_3116_);
    v___x_3120_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1_once),
        _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__1,
    );
    v___x_3121_ = l_Lean_MessageData_ofExpr(v_00_u03c3_3117_);
    v___x_3122_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3122_, 0, v___x_3120_);
    leanh::lean_ctor_set(v___x_3122_, 1, v___x_3121_);
    v___x_3123_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3_once),
        _init_l_Lean_Elab_Do_ControlStack_stateT___lam__0___closed__3,
    );
    v___x_3124_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3124_, 0, v___x_3122_);
    leanh::lean_ctor_set(v___x_3124_, 1, v___x_3123_);
    v___x_3125_ = leanh::lean_box(0);
    v___x_3126_ = leanh::lean_apply_1(v_description_3119_, v___x_3125_);
    v___x_3127_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3127_, 0, v___x_3124_);
    leanh::lean_ctor_set(v___x_3127_, 1, v___x_3126_);
    return v___x_3127_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__1(
    mut v_baseMonadInfo_3128_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3129_: *mut leanh::LeanObject,
    mut v_base_3130_: *mut leanh::LeanObject,
    mut v_00_u03b1_3131_: *mut leanh::LeanObject,
    mut v___y_3132_: *mut leanh::LeanObject,
    mut v___y_3133_: *mut leanh::LeanObject,
    mut v___y_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
    mut v___y_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3140_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(
        v_baseMonadInfo_3128_,
        v_mutVarIdents_3129_,
        v_00_u03b1_3131_,
        v___y_3132_,
        v___y_3133_,
        v___y_3134_,
        v___y_3135_,
        v___y_3136_,
        v___y_3137_,
        v___y_3138_,
    );
    if leanh::lean_obj_tag(v___x_3140_) == 0 {
        let mut v_a_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_stM_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3141_ = leanh::lean_ctor_get(v___x_3140_, 0);
        leanh::lean_inc(v_a_3141_);
        leanh::lean_dec_ref_known(v___x_3140_, 1);
        v_stM_3142_ = leanh::lean_ctor_get(v_base_3130_, 2);
        leanh::lean_inc_ref(v_stM_3142_);
        leanh::lean_dec_ref(v_base_3130_);
        leanh::lean_inc(v___y_3138_);
        leanh::lean_inc_ref(v___y_3137_);
        leanh::lean_inc(v___y_3136_);
        leanh::lean_inc_ref(v___y_3135_);
        leanh::lean_inc(v___y_3134_);
        leanh::lean_inc_ref(v___y_3133_);
        leanh::lean_inc_ref(v___y_3132_);
        v___x_3143_ = leanh::lean_apply_9(
            v_stM_3142_,
            v_a_3141_,
            v___y_3132_,
            v___y_3133_,
            v___y_3134_,
            v___y_3135_,
            v___y_3136_,
            v___y_3137_,
            v___y_3138_,
            leanh::lean_box(0),
        );
        return v___x_3143_;
    } else {
        leanh::lean_dec_ref(v_base_3130_);
        return v___x_3140_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed(
    mut v_baseMonadInfo_3144_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3145_: *mut leanh::LeanObject,
    mut v_base_3146_: *mut leanh::LeanObject,
    mut v_00_u03b1_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
    mut v___y_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3156_ = l_Lean_Elab_Do_ControlStack_stateT___lam__1(
        v_baseMonadInfo_3144_,
        v_mutVarIdents_3145_,
        v_base_3146_,
        v_00_u03b1_3147_,
        v___y_3148_,
        v___y_3149_,
        v___y_3150_,
        v___y_3151_,
        v___y_3152_,
        v___y_3153_,
        v___y_3154_,
    );
    leanh::lean_dec(v___y_3154_);
    leanh::lean_dec_ref(v___y_3153_);
    leanh::lean_dec(v___y_3152_);
    leanh::lean_dec_ref(v___y_3151_);
    leanh::lean_dec(v___y_3150_);
    leanh::lean_dec_ref(v___y_3149_);
    leanh::lean_dec_ref(v___y_3148_);
    return v_res_3156_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__2(
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3158_: *mut leanh::LeanObject,
    mut v_resultName_3159_: *mut leanh::LeanObject,
    mut v_k_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
    mut v___y_3163_: *mut leanh::LeanObject,
    mut v___y_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3169_ = l_Lean_Meta_getFVarFromUserName(
        v_a_3157_,
        v___y_3164_,
        v___y_3165_,
        v___y_3166_,
        v___y_3167_,
    );
    if leanh::lean_obj_tag(v___x_3169_) == 0 {
        let mut v_a_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3170_ = leanh::lean_ctor_get(v___x_3169_, 0);
        leanh::lean_inc(v_a_3170_);
        leanh::lean_dec_ref_known(v___x_3169_, 1);
        v___x_3171_ =
            l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames(
                v_mutVarIdents_3158_,
            );
        v___x_3172_ = lean_array_to_list(v___x_3171_);
        v___x_3173_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3173_, 0, v_resultName_3159_);
        leanh::lean_ctor_set(v___x_3173_, 1, v___x_3172_);
        v___x_3174_ = l_Lean_Expr_fvarId_x21(v_a_3170_);
        leanh::lean_dec(v_a_3170_);
        v___x_3175_ = l_Lean_Elab_Do_bindMutVarsFromTuple(
            v___x_3173_,
            v___x_3174_,
            v_k_3160_,
            v___y_3161_,
            v___y_3162_,
            v___y_3163_,
            v___y_3164_,
            v___y_3165_,
            v___y_3166_,
            v___y_3167_,
        );
        return v___x_3175_;
    } else {
        leanh::lean_dec_ref(v_k_3160_);
        leanh::lean_dec(v_resultName_3159_);
        leanh::lean_dec_ref(v_mutVarIdents_3158_);
        return v___x_3169_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed(
    mut v_a_3176_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3177_: *mut leanh::LeanObject,
    mut v_resultName_3178_: *mut leanh::LeanObject,
    mut v_k_3179_: *mut leanh::LeanObject,
    mut v___y_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: *mut leanh::LeanObject,
    mut v___y_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
    mut v___y_3187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3188_ = l_Lean_Elab_Do_ControlStack_stateT___lam__2(
        v_a_3176_,
        v_mutVarIdents_3177_,
        v_resultName_3178_,
        v_k_3179_,
        v___y_3180_,
        v___y_3181_,
        v___y_3182_,
        v___y_3183_,
        v___y_3184_,
        v___y_3185_,
        v___y_3186_,
    );
    leanh::lean_dec(v___y_3186_);
    leanh::lean_dec_ref(v___y_3185_);
    leanh::lean_dec(v___y_3184_);
    leanh::lean_dec_ref(v___y_3183_);
    leanh::lean_dec(v___y_3182_);
    leanh::lean_dec_ref(v___y_3181_);
    leanh::lean_dec_ref(v___y_3180_);
    return v_res_3188_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__3(
    mut v_baseMonadInfo_3192_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3193_: *mut leanh::LeanObject,
    mut v_base_3194_: *mut leanh::LeanObject,
    mut v_dec_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___y_3200_: *mut leanh::LeanObject,
    mut v___y_3201_: *mut leanh::LeanObject,
    mut v___y_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultName_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreCont_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v_a_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3234_: u8 = 0;
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3204_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3___closed__1;
                v___x_3205_ = l_Lean_Core_mkFreshUserName(v___x_3204_, v___y_3201_, v___y_3202_);
                if leanh::lean_obj_tag(v___x_3205_) == 0 {
                    v_a_3206_ = leanh::lean_ctor_get(v___x_3205_, 0);
                    leanh::lean_inc(v_a_3206_);
                    leanh::lean_dec_ref_known(v___x_3205_, 1);
                    v_resultName_3207_ = leanh::lean_ctor_get(v_dec_3195_, 0);
                    v_resultType_3208_ = leanh::lean_ctor_get(v_dec_3195_, 1);
                    v_k_3209_ = leanh::lean_ctor_get(v_dec_3195_, 2);
                    v_isSharedCheck_3230_ = (!leanh::lean_is_exclusive(v_dec_3195_)) as u8;
                    if v_isSharedCheck_3230_ == 0 {
                        v___x_3211_ = v_dec_3195_;
                        v_isShared_3212_ = v_isSharedCheck_3230_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3209_);
                        leanh::lean_inc(v_resultType_3208_);
                        leanh::lean_inc(v_resultName_3207_);
                        leanh::lean_dec(v_dec_3195_);
                        v___x_3211_ = leanh::lean_box(0);
                        v_isShared_3212_ = v_isSharedCheck_3230_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_dec_3195_);
                    leanh::lean_dec_ref(v_base_3194_);
                    leanh::lean_dec_ref(v_mutVarIdents_3193_);
                    leanh::lean_dec_ref(v_baseMonadInfo_3192_);
                    v_a_3231_ = leanh::lean_ctor_get(v___x_3205_, 0);
                    v_isSharedCheck_3238_ = (!leanh::lean_is_exclusive(v___x_3205_)) as u8;
                    if v_isSharedCheck_3238_ == 0 {
                        v___x_3233_ = v___x_3205_;
                        v_isShared_3234_ = v_isSharedCheck_3238_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3231_);
                        leanh::lean_dec(v___x_3205_);
                        v___x_3233_ = leanh::lean_box(0);
                        v_isShared_3234_ = v_isSharedCheck_3238_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_mutVarIdents_3193_);
                v___x_3213_ =
                    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_stM(
                        v_baseMonadInfo_3192_,
                        v_mutVarIdents_3193_,
                        v_resultType_3208_,
                        v___y_3196_,
                        v___y_3197_,
                        v___y_3198_,
                        v___y_3199_,
                        v___y_3200_,
                        v___y_3201_,
                        v___y_3202_,
                    );
                if leanh::lean_obj_tag(v___x_3213_) == 0 {
                    v_a_3214_ = leanh::lean_ctor_get(v___x_3213_, 0);
                    leanh::lean_inc(v_a_3214_);
                    leanh::lean_dec_ref_known(v___x_3213_, 1);
                    v_restoreCont_3215_ = leanh::lean_ctor_get(v_base_3194_, 4);
                    leanh::lean_inc_ref(v_restoreCont_3215_);
                    leanh::lean_dec_ref(v_base_3194_);
                    leanh::lean_inc(v_a_3206_);
                    v___f_3216_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_ControlStack_stateT___lam__2___boxed
                            as *mut core::ffi::c_void,
                        12,
                        4,
                    );
                    leanh::lean_closure_set(v___f_3216_, 0, v_a_3206_);
                    leanh::lean_closure_set(v___f_3216_, 1, v_mutVarIdents_3193_);
                    leanh::lean_closure_set(v___f_3216_, 2, v_resultName_3207_);
                    leanh::lean_closure_set(v___f_3216_, 3, v_k_3209_);
                    v___x_3217_ = 0;
                    if v_isShared_3212_ == 0 {
                        leanh::lean_ctor_set(v___x_3211_, 2, v___f_3216_);
                        leanh::lean_ctor_set(v___x_3211_, 1, v_a_3214_);
                        leanh::lean_ctor_set(v___x_3211_, 0, v_a_3206_);
                        v___x_3219_ = v___x_3211_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3221_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3206_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_a_3214_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 2, v___f_3216_);
                        v___x_3219_ = v_reuseFailAlloc_3221_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3211_);
                    leanh::lean_dec_ref(v_k_3209_);
                    leanh::lean_dec(v_resultName_3207_);
                    leanh::lean_dec(v_a_3206_);
                    leanh::lean_dec_ref(v_base_3194_);
                    leanh::lean_dec_ref(v_mutVarIdents_3193_);
                    v_a_3222_ = leanh::lean_ctor_get(v___x_3213_, 0);
                    v_isSharedCheck_3229_ = (!leanh::lean_is_exclusive(v___x_3213_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v___x_3224_ = v___x_3213_;
                        v_isShared_3225_ = v_isSharedCheck_3229_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3222_);
                        leanh::lean_dec(v___x_3213_);
                        v___x_3224_ = leanh::lean_box(0);
                        v_isShared_3225_ = v_isSharedCheck_3229_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3219_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3217_,
                );
                leanh::lean_inc(v___y_3202_);
                leanh::lean_inc_ref(v___y_3201_);
                leanh::lean_inc(v___y_3200_);
                leanh::lean_inc_ref(v___y_3199_);
                leanh::lean_inc(v___y_3198_);
                leanh::lean_inc_ref(v___y_3197_);
                leanh::lean_inc_ref(v___y_3196_);
                v___x_3220_ = leanh::lean_apply_9(
                    v_restoreCont_3215_,
                    v___x_3219_,
                    v___y_3196_,
                    v___y_3197_,
                    v___y_3198_,
                    v___y_3199_,
                    v___y_3200_,
                    v___y_3201_,
                    v___y_3202_,
                    leanh::lean_box(0),
                );
                return v___x_3220_;
            }
            3 => {
                if v_isShared_3225_ == 0 {
                    v___x_3227_ = v___x_3224_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
                    v___x_3227_ = v_reuseFailAlloc_3228_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3227_;
            }
            5 => {
                if v_isShared_3234_ == 0 {
                    v___x_3236_ = v___x_3233_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3237_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
                    v___x_3236_ = v_reuseFailAlloc_3237_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed(
    mut v_baseMonadInfo_3239_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3240_: *mut leanh::LeanObject,
    mut v_base_3241_: *mut leanh::LeanObject,
    mut v_dec_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
    mut v___y_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3251_ = l_Lean_Elab_Do_ControlStack_stateT___lam__3(
        v_baseMonadInfo_3239_,
        v_mutVarIdents_3240_,
        v_base_3241_,
        v_dec_3242_,
        v___y_3243_,
        v___y_3244_,
        v___y_3245_,
        v___y_3246_,
        v___y_3247_,
        v___y_3248_,
        v___y_3249_,
    );
    leanh::lean_dec(v___y_3249_);
    leanh::lean_dec_ref(v___y_3248_);
    leanh::lean_dec(v___y_3247_);
    leanh::lean_dec_ref(v___y_3246_);
    leanh::lean_dec(v___y_3245_);
    leanh::lean_dec_ref(v___y_3244_);
    leanh::lean_dec_ref(v___y_3243_);
    return v_res_3251_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(
    mut v_sz_3252_: usize,
    mut v_i_3253_: usize,
    mut v_bs_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
    mut v___y_3257_: *mut leanh::LeanObject,
    mut v___y_3258_: *mut leanh::LeanObject,
    mut v___y_3259_: *mut leanh::LeanObject,
    mut v___y_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: u8 = 0;
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3282_: u8 = 0;
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_a_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3262_ = lean_usize_dec_lt(v_i_3253_, v_sz_3252_);
                if v___x_3262_ == 0 {
                    v___x_3263_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3263_, 0, v_bs_3254_);
                    return v___x_3263_;
                } else {
                    v_v_3264_ = lean_array_uget_borrowed(v_bs_3254_, v_i_3253_);
                    v___x_3265_ = l_Lean_Syntax_getId(v_v_3264_);
                    v___x_3266_ = l_Lean_Meta_getLocalDeclFromUserName(
                        v___x_3265_,
                        v___y_3257_,
                        v___y_3258_,
                        v___y_3259_,
                        v___y_3260_,
                    );
                    if leanh::lean_obj_tag(v___x_3266_) == 0 {
                        v_a_3267_ = leanh::lean_ctor_get(v___x_3266_, 0);
                        leanh::lean_inc(v_a_3267_);
                        leanh::lean_dec_ref_known(v___x_3266_, 1);
                        v___x_3268_ = l_Lean_LocalDecl_toExpr(v_a_3267_);
                        v___x_3269_ = leanh::lean_box(0);
                        v___x_3270_ = leanh::lean_box(0);
                        v___x_3271_ = 0;
                        leanh::lean_inc_ref(v___x_3268_);
                        leanh::lean_inc(v_v_3264_);
                        v___x_3272_ = l_Lean_Elab_Term_addTermInfo_x27(
                            v_v_3264_,
                            v___x_3268_,
                            v___x_3269_,
                            v___x_3269_,
                            v___x_3270_,
                            v___x_3271_,
                            v___x_3271_,
                            v___y_3255_,
                            v___y_3256_,
                            v___y_3257_,
                            v___y_3258_,
                            v___y_3259_,
                            v___y_3260_,
                        );
                        if leanh::lean_obj_tag(v___x_3272_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3272_, 1);
                            v___x_3273_ = leanh::lean_unsigned_to_nat(0);
                            v_bs_x27_3274_ = lean_array_uset(v_bs_3254_, v_i_3253_, v___x_3273_);
                            v___x_3275_ = 1usize;
                            v___x_3276_ = lean_usize_add(v_i_3253_, v___x_3275_);
                            v___x_3277_ = lean_array_uset(v_bs_x27_3274_, v_i_3253_, v___x_3268_);
                            v_i_3253_ = v___x_3276_;
                            v_bs_3254_ = v___x_3277_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_3268_);
                            leanh::lean_dec_ref(v_bs_3254_);
                            v_a_3279_ = leanh::lean_ctor_get(v___x_3272_, 0);
                            v_isSharedCheck_3286_ =
                                (!leanh::lean_is_exclusive(v___x_3272_)) as u8;
                            if v_isSharedCheck_3286_ == 0 {
                                v___x_3281_ = v___x_3272_;
                                v_isShared_3282_ = v_isSharedCheck_3286_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3279_);
                                leanh::lean_dec(v___x_3272_);
                                v___x_3281_ = leanh::lean_box(0);
                                v_isShared_3282_ = v_isSharedCheck_3286_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_bs_3254_);
                        v_a_3287_ = leanh::lean_ctor_get(v___x_3266_, 0);
                        v_isSharedCheck_3294_ =
                            (!leanh::lean_is_exclusive(v___x_3266_)) as u8;
                        if v_isSharedCheck_3294_ == 0 {
                            v___x_3289_ = v___x_3266_;
                            v_isShared_3290_ = v_isSharedCheck_3294_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3287_);
                            leanh::lean_dec(v___x_3266_);
                            v___x_3289_ = leanh::lean_box(0);
                            v_isShared_3290_ = v_isSharedCheck_3294_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3282_ == 0 {
                    v___x_3284_ = v___x_3281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
                    v___x_3284_ = v_reuseFailAlloc_3285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3284_;
            }
            3 => {
                if v_isShared_3290_ == 0 {
                    v___x_3292_ = v___x_3289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg___boxed(
    mut v_sz_3295_: *mut leanh::LeanObject,
    mut v_i_3296_: *mut leanh::LeanObject,
    mut v_bs_3297_: *mut leanh::LeanObject,
    mut v___y_3298_: *mut leanh::LeanObject,
    mut v___y_3299_: *mut leanh::LeanObject,
    mut v___y_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3305_: usize = 0;
    let mut v_i_boxed_3306_: usize = 0;
    let mut v_res_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3305_ = leanh::lean_unbox_usize(v_sz_3295_);
    leanh::lean_dec(v_sz_3295_);
    v_i_boxed_3306_ = leanh::lean_unbox_usize(v_i_3296_);
    leanh::lean_dec(v_i_3296_);
    v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_boxed_3305_, v_i_boxed_3306_, v_bs_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
    leanh::lean_dec(v___y_3303_);
    leanh::lean_dec_ref(v___y_3302_);
    leanh::lean_dec(v___y_3301_);
    leanh::lean_dec_ref(v___y_3300_);
    leanh::lean_dec(v___y_3299_);
    leanh::lean_dec_ref(v___y_3298_);
    return v_res_3307_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3309_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__0;
    v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
    return v___x_3310_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__2;
    v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
    return v___x_3313_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3315_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__4;
    v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
    return v___x_3316_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__4(
    mut v_mutVarIdents_3317_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3318_: *mut leanh::LeanObject,
    mut v_00_u03c3_3319_: *mut leanh::LeanObject,
    mut v_base_3320_: *mut leanh::LeanObject,
    mut v_e_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
    mut v___y_3323_: *mut leanh::LeanObject,
    mut v___y_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
    mut v___y_3326_: *mut leanh::LeanObject,
    mut v___y_3327_: *mut leanh::LeanObject,
    mut v___y_3328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_3330_: usize = 0;
    let mut v___x_3331_: usize = 0;
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___y_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_runInBase_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u8 = 0;
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v_reuseFailAlloc_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_a_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3388_: u8 = 0;
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut v_a_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3396_: u8 = 0;
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_3330_ = lean_array_size(v_mutVarIdents_3317_);
                v___x_3331_ = 0usize;
                v___x_3332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_3330_, v___x_3331_, v_mutVarIdents_3317_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
                if leanh::lean_obj_tag(v___x_3332_) == 0 {
                    v_a_3333_ = leanh::lean_ctor_get(v___x_3332_, 0);
                    leanh::lean_inc(v_a_3333_);
                    leanh::lean_dec_ref_known(v___x_3332_, 1);
                    v_u_3334_ = leanh::lean_ctor_get(v_baseMonadInfo_3318_, 1);
                    leanh::lean_inc(v_u_3334_);
                    leanh::lean_dec_ref(v_baseMonadInfo_3318_);
                    v___x_3335_ = l_Lean_Meta_mkProdMkN(
                        v_a_3333_,
                        v_u_3334_,
                        v___y_3325_,
                        v___y_3326_,
                        v___y_3327_,
                        v___y_3328_,
                    );
                    if leanh::lean_obj_tag(v___x_3335_) == 0 {
                        v_a_3336_ = leanh::lean_ctor_get(v___x_3335_, 0);
                        leanh::lean_inc(v_a_3336_);
                        leanh::lean_dec_ref_known(v___x_3335_, 1);
                        v_fst_3337_ = leanh::lean_ctor_get(v_a_3336_, 0);
                        v_snd_3338_ = leanh::lean_ctor_get(v_a_3336_, 1);
                        v_isSharedCheck_3384_ = (!leanh::lean_is_exclusive(v_a_3336_)) as u8;
                        if v_isSharedCheck_3384_ == 0 {
                            v___x_3340_ = v_a_3336_;
                            v_isShared_3341_ = v_isSharedCheck_3384_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3338_);
                            leanh::lean_inc(v_fst_3337_);
                            leanh::lean_dec(v_a_3336_);
                            v___x_3340_ = leanh::lean_box(0);
                            v_isShared_3341_ = v_isSharedCheck_3384_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3321_);
                        leanh::lean_dec_ref(v_base_3320_);
                        leanh::lean_dec_ref(v_00_u03c3_3319_);
                        v_a_3385_ = leanh::lean_ctor_get(v___x_3335_, 0);
                        v_isSharedCheck_3392_ =
                            (!leanh::lean_is_exclusive(v___x_3335_)) as u8;
                        if v_isSharedCheck_3392_ == 0 {
                            v___x_3387_ = v___x_3335_;
                            v_isShared_3388_ = v_isSharedCheck_3392_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3385_);
                            leanh::lean_dec(v___x_3335_);
                            v___x_3387_ = leanh::lean_box(0);
                            v_isShared_3388_ = v_isSharedCheck_3392_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3321_);
                    leanh::lean_dec_ref(v_base_3320_);
                    leanh::lean_dec_ref(v_00_u03c3_3319_);
                    leanh::lean_dec_ref(v_baseMonadInfo_3318_);
                    v_a_3393_ = leanh::lean_ctor_get(v___x_3332_, 0);
                    v_isSharedCheck_3400_ = (!leanh::lean_is_exclusive(v___x_3332_)) as u8;
                    if v_isSharedCheck_3400_ == 0 {
                        v___x_3395_ = v___x_3332_;
                        v_isShared_3396_ = v_isSharedCheck_3400_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3393_);
                        leanh::lean_dec(v___x_3332_);
                        v___x_3395_ = leanh::lean_box(0);
                        v_isShared_3396_ = v_isSharedCheck_3400_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_00_u03c3_3319_);
                leanh::lean_inc(v_snd_3338_);
                v___x_3353_ = l_Lean_Meta_isExprDefEq(
                    v_snd_3338_,
                    v_00_u03c3_3319_,
                    v___y_3325_,
                    v___y_3326_,
                    v___y_3327_,
                    v___y_3328_,
                );
                if leanh::lean_obj_tag(v___x_3353_) == 0 {
                    v_a_3354_ = leanh::lean_ctor_get(v___x_3353_, 0);
                    leanh::lean_inc(v_a_3354_);
                    leanh::lean_dec_ref_known(v___x_3353_, 1);
                    v___x_3355_ = (leanh::lean_unbox(v_a_3354_) as u8);
                    leanh::lean_dec(v_a_3354_);
                    if v___x_3355_ == 0 {
                        leanh::lean_dec(v_fst_3337_);
                        leanh::lean_dec_ref(v_e_3321_);
                        leanh::lean_dec_ref(v_base_3320_);
                        v___x_3356_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1_once
                            ),
                            _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__1,
                        );
                        v___x_3357_ = l_Lean_MessageData_ofExpr(v_00_u03c3_3319_);
                        if v_isShared_3341_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_3340_, 7);
                            leanh::lean_ctor_set(v___x_3340_, 1, v___x_3357_);
                            leanh::lean_ctor_set(v___x_3340_, 0, v___x_3356_);
                            v___x_3359_ = v___x_3340_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3375_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3356_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3357_);
                            v___x_3359_ = v_reuseFailAlloc_3375_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3340_);
                        leanh::lean_dec(v_snd_3338_);
                        leanh::lean_dec_ref(v_00_u03c3_3319_);
                        v___y_3343_ = v___y_3322_;
                        v___y_3344_ = v___y_3323_;
                        v___y_3345_ = v___y_3324_;
                        v___y_3346_ = v___y_3325_;
                        v___y_3347_ = v___y_3326_;
                        v___y_3348_ = v___y_3327_;
                        v___y_3349_ = v___y_3328_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3340_);
                    leanh::lean_dec(v_snd_3338_);
                    leanh::lean_dec(v_fst_3337_);
                    leanh::lean_dec_ref(v_e_3321_);
                    leanh::lean_dec_ref(v_base_3320_);
                    leanh::lean_dec_ref(v_00_u03c3_3319_);
                    v_a_3376_ = leanh::lean_ctor_get(v___x_3353_, 0);
                    v_isSharedCheck_3383_ = (!leanh::lean_is_exclusive(v___x_3353_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v___x_3378_ = v___x_3353_;
                        v_isShared_3379_ = v_isSharedCheck_3383_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3376_);
                        leanh::lean_dec(v___x_3353_);
                        v___x_3378_ = leanh::lean_box(0);
                        v_isShared_3379_ = v_isSharedCheck_3383_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_runInBase_3350_ = leanh::lean_ctor_get(v_base_3320_, 3);
                leanh::lean_inc_ref(v_runInBase_3350_);
                leanh::lean_dec_ref(v_base_3320_);
                v___x_3351_ = l_Lean_Expr_app___override(v_e_3321_, v_fst_3337_);
                leanh::lean_inc(v___y_3349_);
                leanh::lean_inc_ref(v___y_3348_);
                leanh::lean_inc(v___y_3347_);
                leanh::lean_inc_ref(v___y_3346_);
                leanh::lean_inc(v___y_3345_);
                leanh::lean_inc_ref(v___y_3344_);
                leanh::lean_inc_ref(v___y_3343_);
                v___x_3352_ = leanh::lean_apply_9(
                    v_runInBase_3350_,
                    v___x_3351_,
                    v___y_3343_,
                    v___y_3344_,
                    v___y_3345_,
                    v___y_3346_,
                    v___y_3347_,
                    v___y_3348_,
                    v___y_3349_,
                    leanh::lean_box(0),
                );
                return v___x_3352_;
            }
            3 => {
                v___x_3360_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3_once
                    ),
                    _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__3,
                );
                v___x_3361_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3361_, 0, v___x_3359_);
                leanh::lean_ctor_set(v___x_3361_, 1, v___x_3360_);
                v___x_3362_ = l_Lean_MessageData_ofExpr(v_snd_3338_);
                v___x_3363_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3363_, 0, v___x_3361_);
                leanh::lean_ctor_set(v___x_3363_, 1, v___x_3362_);
                v___x_3364_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5_once
                    ),
                    _init_l_Lean_Elab_Do_ControlStack_stateT___lam__4___closed__5,
                );
                v___x_3365_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3365_, 0, v___x_3363_);
                leanh::lean_ctor_set(v___x_3365_, 1, v___x_3364_);
                v___x_3366_ =
                    l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
                        v___x_3365_,
                        v___y_3325_,
                        v___y_3326_,
                        v___y_3327_,
                        v___y_3328_,
                    );
                v_a_3367_ = leanh::lean_ctor_get(v___x_3366_, 0);
                v_isSharedCheck_3374_ = (!leanh::lean_is_exclusive(v___x_3366_)) as u8;
                if v_isSharedCheck_3374_ == 0 {
                    v___x_3369_ = v___x_3366_;
                    v_isShared_3370_ = v_isSharedCheck_3374_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3367_);
                    leanh::lean_dec(v___x_3366_);
                    v___x_3369_ = leanh::lean_box(0);
                    v_isShared_3370_ = v_isSharedCheck_3374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3370_ == 0 {
                    v___x_3372_ = v___x_3369_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
                    v___x_3372_ = v_reuseFailAlloc_3373_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3372_;
            }
            6 => {
                if v_isShared_3379_ == 0 {
                    v___x_3381_ = v___x_3378_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
                    v___x_3381_ = v_reuseFailAlloc_3382_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3381_;
            }
            8 => {
                if v_isShared_3388_ == 0 {
                    v___x_3390_ = v___x_3387_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
                    v___x_3390_ = v_reuseFailAlloc_3391_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3390_;
            }
            10 => {
                if v_isShared_3396_ == 0 {
                    v___x_3398_ = v___x_3395_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3399_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
                    v___x_3398_ = v_reuseFailAlloc_3399_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed(
    mut v_mutVarIdents_3401_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3402_: *mut leanh::LeanObject,
    mut v_00_u03c3_3403_: *mut leanh::LeanObject,
    mut v_base_3404_: *mut leanh::LeanObject,
    mut v_e_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
    mut v___y_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3414_ = l_Lean_Elab_Do_ControlStack_stateT___lam__4(
        v_mutVarIdents_3401_,
        v_baseMonadInfo_3402_,
        v_00_u03c3_3403_,
        v_base_3404_,
        v_e_3405_,
        v___y_3406_,
        v___y_3407_,
        v___y_3408_,
        v___y_3409_,
        v___y_3410_,
        v___y_3411_,
        v___y_3412_,
    );
    leanh::lean_dec(v___y_3412_);
    leanh::lean_dec_ref(v___y_3411_);
    leanh::lean_dec(v___y_3410_);
    leanh::lean_dec_ref(v___y_3409_);
    leanh::lean_dec(v___y_3408_);
    leanh::lean_dec_ref(v___y_3407_);
    leanh::lean_dec_ref(v___y_3406_);
    return v_res_3414_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__5(
    mut v_baseMonadInfo_3418_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3419_: *mut leanh::LeanObject,
    mut v_base_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
    mut v___y_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v_u_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_baseMonadInfo_3418_);
                v___x_3429_ =
                    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3(
                        v_baseMonadInfo_3418_,
                        v_mutVarIdents_3419_,
                        v___y_3421_,
                        v___y_3422_,
                        v___y_3423_,
                        v___y_3424_,
                        v___y_3425_,
                        v___y_3426_,
                        v___y_3427_,
                    );
                if leanh::lean_obj_tag(v___x_3429_) == 0 {
                    v_a_3430_ = leanh::lean_ctor_get(v___x_3429_, 0);
                    leanh::lean_inc(v_a_3430_);
                    leanh::lean_dec_ref_known(v___x_3429_, 1);
                    v_m_3431_ = leanh::lean_ctor_get(v_base_3420_, 1);
                    leanh::lean_inc_ref(v_m_3431_);
                    leanh::lean_dec_ref(v_base_3420_);
                    leanh::lean_inc(v___y_3427_);
                    leanh::lean_inc_ref(v___y_3426_);
                    leanh::lean_inc(v___y_3425_);
                    leanh::lean_inc_ref(v___y_3424_);
                    leanh::lean_inc(v___y_3423_);
                    leanh::lean_inc_ref(v___y_3422_);
                    leanh::lean_inc_ref(v___y_3421_);
                    v___x_3432_ = leanh::lean_apply_8(
                        v_m_3431_,
                        v___y_3421_,
                        v___y_3422_,
                        v___y_3423_,
                        v___y_3424_,
                        v___y_3425_,
                        v___y_3426_,
                        v___y_3427_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3432_) == 0 {
                        v_a_3433_ = leanh::lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3448_ =
                            (!leanh::lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3448_ == 0 {
                            v___x_3435_ = v___x_3432_;
                            v_isShared_3436_ = v_isSharedCheck_3448_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3433_);
                            leanh::lean_dec(v___x_3432_);
                            v___x_3435_ = leanh::lean_box(0);
                            v_isShared_3436_ = v_isSharedCheck_3448_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3430_);
                        leanh::lean_dec_ref(v_baseMonadInfo_3418_);
                        return v___x_3432_;
                    }
                } else {
                    leanh::lean_dec_ref(v_base_3420_);
                    leanh::lean_dec_ref(v_baseMonadInfo_3418_);
                    return v___x_3429_;
                }
            }
            1 => {
                v_u_3437_ = leanh::lean_ctor_get(v_baseMonadInfo_3418_, 1);
                leanh::lean_inc(v_u_3437_);
                v_v_3438_ = leanh::lean_ctor_get(v_baseMonadInfo_3418_, 2);
                leanh::lean_inc(v_v_3438_);
                leanh::lean_dec_ref(v_baseMonadInfo_3418_);
                v___x_3439_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5___closed__1;
                v___x_3440_ = leanh::lean_box(0);
                v___x_3441_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3441_, 0, v_v_3438_);
                leanh::lean_ctor_set(v___x_3441_, 1, v___x_3440_);
                v___x_3442_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3442_, 0, v_u_3437_);
                leanh::lean_ctor_set(v___x_3442_, 1, v___x_3441_);
                v___x_3443_ = l_Lean_mkConst(v___x_3439_, v___x_3442_);
                v___x_3444_ = l_Lean_mkAppB(v___x_3443_, v_a_3430_, v_a_3433_);
                if v_isShared_3436_ == 0 {
                    leanh::lean_ctor_set(v___x_3435_, 0, v___x_3444_);
                    v___x_3446_ = v___x_3435_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
                    v___x_3446_ = v_reuseFailAlloc_3447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed(
    mut v_baseMonadInfo_3449_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3450_: *mut leanh::LeanObject,
    mut v_base_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
    mut v___y_3453_: *mut leanh::LeanObject,
    mut v___y_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_Lean_Elab_Do_ControlStack_stateT___lam__5(
        v_baseMonadInfo_3449_,
        v_mutVarIdents_3450_,
        v_base_3451_,
        v___y_3452_,
        v___y_3453_,
        v___y_3454_,
        v___y_3455_,
        v___y_3456_,
        v___y_3457_,
        v___y_3458_,
    );
    leanh::lean_dec(v___y_3458_);
    leanh::lean_dec_ref(v___y_3457_);
    leanh::lean_dec(v___y_3456_);
    leanh::lean_dec_ref(v___y_3455_);
    leanh::lean_dec(v___y_3454_);
    leanh::lean_dec_ref(v___y_3453_);
    leanh::lean_dec_ref(v___y_3452_);
    return v_res_3460_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_stateT(
    mut v_baseMonadInfo_3461_: *mut leanh::LeanObject,
    mut v_mutVarIdents_3462_: *mut leanh::LeanObject,
    mut v_00_u03c3_3463_: *mut leanh::LeanObject,
    mut v_base_3464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_00_u03c3_3463_);
    leanh::lean_inc_ref_n(v_base_3464_, 4);
    v___f_3465_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_ControlStack_stateT___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3465_, 0, v_base_3464_);
    leanh::lean_closure_set(v___f_3465_, 1, v_00_u03c3_3463_);
    leanh::lean_inc_ref_n(v_mutVarIdents_3462_, 3);
    leanh::lean_inc_ref_n(v_baseMonadInfo_3461_, 3);
    v___f_3466_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_ControlStack_stateT___lam__1___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    leanh::lean_closure_set(v___f_3466_, 0, v_baseMonadInfo_3461_);
    leanh::lean_closure_set(v___f_3466_, 1, v_mutVarIdents_3462_);
    leanh::lean_closure_set(v___f_3466_, 2, v_base_3464_);
    v___f_3467_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_ControlStack_stateT___lam__3___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    leanh::lean_closure_set(v___f_3467_, 0, v_baseMonadInfo_3461_);
    leanh::lean_closure_set(v___f_3467_, 1, v_mutVarIdents_3462_);
    leanh::lean_closure_set(v___f_3467_, 2, v_base_3464_);
    v___f_3468_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_ControlStack_stateT___lam__4___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    leanh::lean_closure_set(v___f_3468_, 0, v_mutVarIdents_3462_);
    leanh::lean_closure_set(v___f_3468_, 1, v_baseMonadInfo_3461_);
    leanh::lean_closure_set(v___f_3468_, 2, v_00_u03c3_3463_);
    leanh::lean_closure_set(v___f_3468_, 3, v_base_3464_);
    v___f_3469_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_ControlStack_stateT___lam__5___boxed as *mut core::ffi::c_void,
        11,
        3,
    );
    leanh::lean_closure_set(v___f_3469_, 0, v_baseMonadInfo_3461_);
    leanh::lean_closure_set(v___f_3469_, 1, v_mutVarIdents_3462_);
    leanh::lean_closure_set(v___f_3469_, 2, v_base_3464_);
    v___x_3470_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3470_, 0, v___f_3465_);
    leanh::lean_ctor_set(v___x_3470_, 1, v___f_3469_);
    leanh::lean_ctor_set(v___x_3470_, 2, v___f_3466_);
    leanh::lean_ctor_set(v___x_3470_, 3, v___f_3468_);
    leanh::lean_ctor_set(v___x_3470_, 4, v___f_3467_);
    return v___x_3470_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(
    mut v_sz_3471_: usize,
    mut v_i_3472_: usize,
    mut v_bs_3473_: *mut leanh::LeanObject,
    mut v___y_3474_: *mut leanh::LeanObject,
    mut v___y_3475_: *mut leanh::LeanObject,
    mut v___y_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
    mut v___y_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___redArg(v_sz_3471_, v_i_3472_, v_bs_3473_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
    return v___x_3482_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0___boxed(
    mut v_sz_3483_: *mut leanh::LeanObject,
    mut v_i_3484_: *mut leanh::LeanObject,
    mut v_bs_3485_: *mut leanh::LeanObject,
    mut v___y_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
    mut v___y_3488_: *mut leanh::LeanObject,
    mut v___y_3489_: *mut leanh::LeanObject,
    mut v___y_3490_: *mut leanh::LeanObject,
    mut v___y_3491_: *mut leanh::LeanObject,
    mut v___y_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3494_: usize = 0;
    let mut v_i_boxed_3495_: usize = 0;
    let mut v_res_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3494_ = leanh::lean_unbox_usize(v_sz_3483_);
    leanh::lean_dec(v_sz_3483_);
    v_i_boxed_3495_ = leanh::lean_unbox_usize(v_i_3484_);
    leanh::lean_dec(v_i_3484_);
    v_res_3496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_ControlStack_stateT_spec__0(v_sz_boxed_3494_, v_i_boxed_3495_, v_bs_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
    leanh::lean_dec(v___y_3492_);
    leanh::lean_dec_ref(v___y_3491_);
    leanh::lean_dec(v___y_3490_);
    leanh::lean_dec_ref(v___y_3489_);
    leanh::lean_dec(v___y_3488_);
    leanh::lean_dec_ref(v___y_3487_);
    leanh::lean_dec_ref(v___y_3486_);
    return v_res_3496_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(
    mut v_baseMonadInfo_3500_: *mut leanh::LeanObject,
    mut v_00_u03b1_3501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_u_3502_ = leanh::lean_ctor_get(v_baseMonadInfo_3500_, 1);
    v___x_3503_ =
        l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1;
    v___x_3504_ = leanh::lean_box(0);
    leanh::lean_inc(v_u_3502_);
    v___x_3505_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3505_, 0, v_u_3502_);
    leanh::lean_ctor_set(v___x_3505_, 1, v___x_3504_);
    v___x_3506_ = l_Lean_mkConst(v___x_3503_, v___x_3505_);
    v___x_3507_ = l_Lean_Expr_app___override(v___x_3506_, v_00_u03b1_3501_);
    return v___x_3507_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___boxed(
    mut v_baseMonadInfo_3508_: *mut leanh::LeanObject,
    mut v_00_u03b1_3509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3510_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(
        v_baseMonadInfo_3508_,
        v_00_u03b1_3509_,
    );
    leanh::lean_dec_ref(v_baseMonadInfo_3508_);
    return v_res_3510_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__0(
    mut v_runInBase_3516_: *mut leanh::LeanObject,
    mut v_e_3517_: *mut leanh::LeanObject,
    mut v___y_3518_: *mut leanh::LeanObject,
    mut v___y_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
    mut v___y_3521_: *mut leanh::LeanObject,
    mut v___y_3522_: *mut leanh::LeanObject,
    mut v___y_3523_: *mut leanh::LeanObject,
    mut v___y_3524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0___closed__2;
    v___x_3527_ = leanh::lean_unsigned_to_nat(1);
    v___x_3528_ = lean_mk_empty_array_with_capacity(v___x_3527_);
    v___x_3529_ = lean_array_push(v___x_3528_, v_e_3517_);
    v___x_3530_ = l_Lean_Meta_mkAppM(
        v___x_3526_,
        v___x_3529_,
        v___y_3521_,
        v___y_3522_,
        v___y_3523_,
        v___y_3524_,
    );
    if leanh::lean_obj_tag(v___x_3530_) == 0 {
        let mut v_a_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3531_ = leanh::lean_ctor_get(v___x_3530_, 0);
        leanh::lean_inc(v_a_3531_);
        leanh::lean_dec_ref_known(v___x_3530_, 1);
        leanh::lean_inc(v___y_3524_);
        leanh::lean_inc_ref(v___y_3523_);
        leanh::lean_inc(v___y_3522_);
        leanh::lean_inc_ref(v___y_3521_);
        leanh::lean_inc(v___y_3520_);
        leanh::lean_inc_ref(v___y_3519_);
        leanh::lean_inc_ref(v___y_3518_);
        v___x_3532_ = leanh::lean_apply_9(
            v_runInBase_3516_,
            v_a_3531_,
            v___y_3518_,
            v___y_3519_,
            v___y_3520_,
            v___y_3521_,
            v___y_3522_,
            v___y_3523_,
            v___y_3524_,
            leanh::lean_box(0),
        );
        return v___x_3532_;
    } else {
        leanh::lean_dec_ref(v_runInBase_3516_);
        return v___x_3530_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed(
    mut v_runInBase_3533_: *mut leanh::LeanObject,
    mut v_e_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
    mut v___y_3539_: *mut leanh::LeanObject,
    mut v___y_3540_: *mut leanh::LeanObject,
    mut v___y_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3543_ = l_Lean_Elab_Do_ControlStack_optionT___lam__0(
        v_runInBase_3533_,
        v_e_3534_,
        v___y_3535_,
        v___y_3536_,
        v___y_3537_,
        v___y_3538_,
        v___y_3539_,
        v___y_3540_,
        v___y_3541_,
    );
    leanh::lean_dec(v___y_3541_);
    leanh::lean_dec_ref(v___y_3540_);
    leanh::lean_dec(v___y_3539_);
    leanh::lean_dec_ref(v___y_3538_);
    leanh::lean_dec(v___y_3537_);
    leanh::lean_dec_ref(v___y_3536_);
    leanh::lean_dec_ref(v___y_3535_);
    return v_res_3543_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3545_ = l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__0;
    v___x_3546_ = l_Lean_stringToMessageData(v___x_3545_);
    return v___x_3546_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__1(
    mut v_description_3547_: *mut leanh::LeanObject,
    mut v_x_3548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3549_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1_once),
        _init_l_Lean_Elab_Do_ControlStack_optionT___lam__1___closed__1,
    );
    v___x_3550_ = leanh::lean_box(0);
    v___x_3551_ = leanh::lean_apply_1(v_description_3547_, v___x_3550_);
    v___x_3552_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3552_, 0, v___x_3549_);
    leanh::lean_ctor_set(v___x_3552_, 1, v___x_3551_);
    return v___x_3552_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__2(
    mut v_k_3553_: *mut leanh::LeanObject,
    mut v_r_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
    mut v___y_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3561_);
    leanh::lean_inc_ref(v___y_3560_);
    leanh::lean_inc(v___y_3559_);
    leanh::lean_inc_ref(v___y_3558_);
    leanh::lean_inc(v___y_3557_);
    leanh::lean_inc_ref(v___y_3556_);
    leanh::lean_inc_ref(v___y_3555_);
    v___x_3563_ = leanh::lean_apply_8(
        v_k_3553_,
        v___y_3555_,
        v___y_3556_,
        v___y_3557_,
        v___y_3558_,
        v___y_3559_,
        v___y_3560_,
        v___y_3561_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_3563_) == 0 {
        let mut v_a_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3568_: u8 = 0;
        let mut v___x_3569_: u8 = 0;
        let mut v___x_3570_: u8 = 0;
        let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3564_ = leanh::lean_ctor_get(v___x_3563_, 0);
        leanh::lean_inc(v_a_3564_);
        leanh::lean_dec_ref_known(v___x_3563_, 1);
        v___x_3565_ = leanh::lean_unsigned_to_nat(1);
        v___x_3566_ = lean_mk_empty_array_with_capacity(v___x_3565_);
        v___x_3567_ = lean_array_push(v___x_3566_, v_r_3554_);
        v___x_3568_ = 0;
        v___x_3569_ = 1;
        v___x_3570_ = 1;
        v___x_3571_ = l_Lean_Meta_mkLambdaFVars(
            v___x_3567_,
            v_a_3564_,
            v___x_3568_,
            v___x_3569_,
            v___x_3568_,
            v___x_3569_,
            v___x_3570_,
            v___y_3558_,
            v___y_3559_,
            v___y_3560_,
            v___y_3561_,
        );
        leanh::lean_dec_ref(v___x_3567_);
        return v___x_3571_;
    } else {
        leanh::lean_dec_ref(v_r_3554_);
        return v___x_3563_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed(
    mut v_k_3572_: *mut leanh::LeanObject,
    mut v_r_3573_: *mut leanh::LeanObject,
    mut v___y_3574_: *mut leanh::LeanObject,
    mut v___y_3575_: *mut leanh::LeanObject,
    mut v___y_3576_: *mut leanh::LeanObject,
    mut v___y_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
    mut v___y_3580_: *mut leanh::LeanObject,
    mut v___y_3581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3582_ = l_Lean_Elab_Do_ControlStack_optionT___lam__2(
        v_k_3572_,
        v_r_3573_,
        v___y_3574_,
        v___y_3575_,
        v___y_3576_,
        v___y_3577_,
        v___y_3578_,
        v___y_3579_,
        v___y_3580_,
    );
    leanh::lean_dec(v___y_3580_);
    leanh::lean_dec_ref(v___y_3579_);
    leanh::lean_dec(v___y_3578_);
    leanh::lean_dec_ref(v___y_3577_);
    leanh::lean_dec(v___y_3576_);
    leanh::lean_dec_ref(v___y_3575_);
    leanh::lean_dec_ref(v___y_3574_);
    return v_res_3582_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__3(
    mut v_a_3583_: *mut leanh::LeanObject,
    mut v_r_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
    mut v___y_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3591_);
    leanh::lean_inc_ref(v___y_3590_);
    leanh::lean_inc(v___y_3589_);
    leanh::lean_inc_ref(v___y_3588_);
    leanh::lean_inc(v___y_3587_);
    leanh::lean_inc_ref(v___y_3586_);
    leanh::lean_inc_ref(v___y_3585_);
    v___x_3593_ = leanh::lean_apply_8(
        v_a_3583_,
        v___y_3585_,
        v___y_3586_,
        v___y_3587_,
        v___y_3588_,
        v___y_3589_,
        v___y_3590_,
        v___y_3591_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_3593_) == 0 {
        let mut v_a_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3598_: u8 = 0;
        let mut v___x_3599_: u8 = 0;
        let mut v___x_3600_: u8 = 0;
        let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3594_ = leanh::lean_ctor_get(v___x_3593_, 0);
        leanh::lean_inc(v_a_3594_);
        leanh::lean_dec_ref_known(v___x_3593_, 1);
        v___x_3595_ = leanh::lean_unsigned_to_nat(1);
        v___x_3596_ = lean_mk_empty_array_with_capacity(v___x_3595_);
        v___x_3597_ = lean_array_push(v___x_3596_, v_r_3584_);
        v___x_3598_ = 0;
        v___x_3599_ = 1;
        v___x_3600_ = 1;
        v___x_3601_ = l_Lean_Meta_mkLambdaFVars(
            v___x_3597_,
            v_a_3594_,
            v___x_3598_,
            v___x_3599_,
            v___x_3598_,
            v___x_3599_,
            v___x_3600_,
            v___y_3588_,
            v___y_3589_,
            v___y_3590_,
            v___y_3591_,
        );
        leanh::lean_dec_ref(v___x_3597_);
        return v___x_3601_;
    } else {
        leanh::lean_dec_ref(v_r_3584_);
        return v___x_3593_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed(
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v_r_3603_: *mut leanh::LeanObject,
    mut v___y_3604_: *mut leanh::LeanObject,
    mut v___y_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
    mut v___y_3607_: *mut leanh::LeanObject,
    mut v___y_3608_: *mut leanh::LeanObject,
    mut v___y_3609_: *mut leanh::LeanObject,
    mut v___y_3610_: *mut leanh::LeanObject,
    mut v___y_3611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ = l_Lean_Elab_Do_ControlStack_optionT___lam__3(
        v_a_3602_,
        v_r_3603_,
        v___y_3604_,
        v___y_3605_,
        v___y_3606_,
        v___y_3607_,
        v___y_3608_,
        v___y_3609_,
        v___y_3610_,
    );
    leanh::lean_dec(v___y_3610_);
    leanh::lean_dec_ref(v___y_3609_);
    leanh::lean_dec(v___y_3608_);
    leanh::lean_dec_ref(v___y_3607_);
    leanh::lean_dec(v___y_3606_);
    leanh::lean_dec_ref(v___y_3605_);
    leanh::lean_dec_ref(v___y_3604_);
    return v_res_3612_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(
    mut v_k_3613_: *mut leanh::LeanObject,
    mut v___y_3614_: *mut leanh::LeanObject,
    mut v___y_3615_: *mut leanh::LeanObject,
    mut v___y_3616_: *mut leanh::LeanObject,
    mut v_b_3617_: *mut leanh::LeanObject,
    mut v___y_3618_: *mut leanh::LeanObject,
    mut v___y_3619_: *mut leanh::LeanObject,
    mut v___y_3620_: *mut leanh::LeanObject,
    mut v___y_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3621_);
    leanh::lean_inc_ref(v___y_3620_);
    leanh::lean_inc(v___y_3619_);
    leanh::lean_inc_ref(v___y_3618_);
    leanh::lean_inc(v___y_3616_);
    leanh::lean_inc_ref(v___y_3615_);
    leanh::lean_inc_ref(v___y_3614_);
    v___x_3623_ = leanh::lean_apply_9(
        v_k_3613_,
        v_b_3617_,
        v___y_3614_,
        v___y_3615_,
        v___y_3616_,
        v___y_3618_,
        v___y_3619_,
        v___y_3620_,
        v___y_3621_,
        leanh::lean_box(0),
    );
    return v___x_3623_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
    mut v___y_3627_: *mut leanh::LeanObject,
    mut v_b_3628_: *mut leanh::LeanObject,
    mut v___y_3629_: *mut leanh::LeanObject,
    mut v___y_3630_: *mut leanh::LeanObject,
    mut v___y_3631_: *mut leanh::LeanObject,
    mut v___y_3632_: *mut leanh::LeanObject,
    mut v___y_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3634_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0(v_k_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v_b_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
    leanh::lean_dec(v___y_3632_);
    leanh::lean_dec_ref(v___y_3631_);
    leanh::lean_dec(v___y_3630_);
    leanh::lean_dec_ref(v___y_3629_);
    leanh::lean_dec(v___y_3627_);
    leanh::lean_dec_ref(v___y_3626_);
    leanh::lean_dec_ref(v___y_3625_);
    return v_res_3634_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(
    mut v_name_3635_: *mut leanh::LeanObject,
    mut v_bi_3636_: u8,
    mut v_type_3637_: *mut leanh::LeanObject,
    mut v_k_3638_: *mut leanh::LeanObject,
    mut v_kind_3639_: u8,
    mut v___y_3640_: *mut leanh::LeanObject,
    mut v___y_3641_: *mut leanh::LeanObject,
    mut v___y_3642_: *mut leanh::LeanObject,
    mut v___y_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
    mut v___y_3645_: *mut leanh::LeanObject,
    mut v___y_3646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3642_);
                leanh::lean_inc_ref(v___y_3641_);
                leanh::lean_inc_ref(v___y_3640_);
                v___f_3648_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                leanh::lean_closure_set(v___f_3648_, 0, v_k_3638_);
                leanh::lean_closure_set(v___f_3648_, 1, v___y_3640_);
                leanh::lean_closure_set(v___f_3648_, 2, v___y_3641_);
                leanh::lean_closure_set(v___f_3648_, 3, v___y_3642_);
                v___x_3649_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_3635_,
                    v_bi_3636_,
                    v_type_3637_,
                    v___f_3648_,
                    v_kind_3639_,
                    v___y_3643_,
                    v___y_3644_,
                    v___y_3645_,
                    v___y_3646_,
                );
                if leanh::lean_obj_tag(v___x_3649_) == 0 {
                    return v___x_3649_;
                } else {
                    v_a_3650_ = leanh::lean_ctor_get(v___x_3649_, 0);
                    v_isSharedCheck_3657_ = (!leanh::lean_is_exclusive(v___x_3649_)) as u8;
                    if v_isSharedCheck_3657_ == 0 {
                        v___x_3652_ = v___x_3649_;
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3650_);
                        leanh::lean_dec(v___x_3649_);
                        v___x_3652_ = leanh::lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3653_ == 0 {
                    v___x_3655_ = v___x_3652_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3656_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
                    v___x_3655_ = v_reuseFailAlloc_3656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg___boxed(
    mut v_name_3658_: *mut leanh::LeanObject,
    mut v_bi_3659_: *mut leanh::LeanObject,
    mut v_type_3660_: *mut leanh::LeanObject,
    mut v_k_3661_: *mut leanh::LeanObject,
    mut v_kind_3662_: *mut leanh::LeanObject,
    mut v___y_3663_: *mut leanh::LeanObject,
    mut v___y_3664_: *mut leanh::LeanObject,
    mut v___y_3665_: *mut leanh::LeanObject,
    mut v___y_3666_: *mut leanh::LeanObject,
    mut v___y_3667_: *mut leanh::LeanObject,
    mut v___y_3668_: *mut leanh::LeanObject,
    mut v___y_3669_: *mut leanh::LeanObject,
    mut v___y_3670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3671_: u8 = 0;
    let mut v_kind_boxed_3672_: u8 = 0;
    let mut v_res_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3671_ = (leanh::lean_unbox(v_bi_3659_) as u8);
    v_kind_boxed_3672_ = (leanh::lean_unbox(v_kind_3662_) as u8);
    v_res_3673_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_3658_, v_bi_boxed_3671_, v_type_3660_, v_k_3661_, v_kind_boxed_3672_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
    leanh::lean_dec(v___y_3669_);
    leanh::lean_dec_ref(v___y_3668_);
    leanh::lean_dec(v___y_3667_);
    leanh::lean_dec_ref(v___y_3666_);
    leanh::lean_dec(v___y_3665_);
    leanh::lean_dec_ref(v___y_3664_);
    leanh::lean_dec_ref(v___y_3663_);
    return v_res_3673_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(
    mut v_name_3674_: *mut leanh::LeanObject,
    mut v_type_3675_: *mut leanh::LeanObject,
    mut v_k_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
    mut v___y_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3685_: u8 = 0;
    let mut v___x_3686_: u8 = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3685_ = 0;
    v___x_3686_ = 0;
    v___x_3687_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_3674_, v___x_3685_, v_type_3675_, v_k_3676_, v___x_3686_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
    return v___x_3687_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg___boxed(
    mut v_name_3688_: *mut leanh::LeanObject,
    mut v_type_3689_: *mut leanh::LeanObject,
    mut v_k_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
    mut v___y_3695_: *mut leanh::LeanObject,
    mut v___y_3696_: *mut leanh::LeanObject,
    mut v___y_3697_: *mut leanh::LeanObject,
    mut v___y_3698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3699_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(
            v_name_3688_,
            v_type_3689_,
            v_k_3690_,
            v___y_3691_,
            v___y_3692_,
            v___y_3693_,
            v___y_3694_,
            v___y_3695_,
            v___y_3696_,
            v___y_3697_,
        );
    leanh::lean_dec(v___y_3697_);
    leanh::lean_dec_ref(v___y_3696_);
    leanh::lean_dec(v___y_3695_);
    leanh::lean_dec_ref(v___y_3694_);
    leanh::lean_dec(v___y_3693_);
    leanh::lean_dec_ref(v___y_3692_);
    leanh::lean_dec_ref(v___y_3691_);
    return v_res_3699_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3706_ = leanh::lean_box(0);
    v___x_3707_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__3;
    v___x_3708_ = l_Lean_mkConst(v___x_3707_, v___x_3706_);
    return v___x_3708_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__4(
    mut v_a_3709_: *mut leanh::LeanObject,
    mut v_getCont_3710_: *mut leanh::LeanObject,
    mut v_resultName_3711_: *mut leanh::LeanObject,
    mut v_resultType_3712_: *mut leanh::LeanObject,
    mut v___f_3713_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3714_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
    mut v___y_3719_: *mut leanh::LeanObject,
    mut v___y_3720_: *mut leanh::LeanObject,
    mut v___y_3721_: *mut leanh::LeanObject,
    mut v___y_3722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v_u_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut v_a_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3757_: u8 = 0;
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v_a_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3724_ = l_Lean_Meta_getFVarFromUserName(
                    v_a_3709_,
                    v___y_3719_,
                    v___y_3720_,
                    v___y_3721_,
                    v___y_3722_,
                );
                if leanh::lean_obj_tag(v___x_3724_) == 0 {
                    v_a_3725_ = leanh::lean_ctor_get(v___x_3724_, 0);
                    leanh::lean_inc(v_a_3725_);
                    leanh::lean_dec_ref_known(v___x_3724_, 1);
                    leanh::lean_inc(v___y_3722_);
                    leanh::lean_inc_ref(v___y_3721_);
                    leanh::lean_inc(v___y_3720_);
                    leanh::lean_inc_ref(v___y_3719_);
                    leanh::lean_inc(v___y_3718_);
                    leanh::lean_inc_ref(v___y_3717_);
                    leanh::lean_inc_ref(v___y_3716_);
                    v___x_3726_ = leanh::lean_apply_8(
                        v_getCont_3710_,
                        v___y_3716_,
                        v___y_3717_,
                        v___y_3718_,
                        v___y_3719_,
                        v___y_3720_,
                        v___y_3721_,
                        v___y_3722_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3726_) == 0 {
                        v_a_3727_ = leanh::lean_ctor_get(v___x_3726_, 0);
                        leanh::lean_inc(v_a_3727_);
                        leanh::lean_dec_ref_known(v___x_3726_, 1);
                        v___x_3728_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1;
                        v___x_3729_ =
                            l_Lean_Core_mkFreshUserName(v___x_3728_, v___y_3721_, v___y_3722_);
                        if leanh::lean_obj_tag(v___x_3729_) == 0 {
                            v_a_3730_ = leanh::lean_ctor_get(v___x_3729_, 0);
                            leanh::lean_inc(v_a_3730_);
                            leanh::lean_dec_ref_known(v___x_3729_, 1);
                            v___f_3731_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_ControlStack_optionT___lam__3___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            leanh::lean_closure_set(v___f_3731_, 0, v_a_3727_);
                            v___x_3732_ = leanh::lean_box(0);
                            v___x_3733_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4_once
                                ),
                                _init_l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__4,
                            );
                            v___x_3734_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_3730_, v___x_3733_, v___f_3731_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
                            if leanh::lean_obj_tag(v___x_3734_) == 0 {
                                v_a_3735_ = leanh::lean_ctor_get(v___x_3734_, 0);
                                leanh::lean_inc(v_a_3735_);
                                leanh::lean_dec_ref_known(v___x_3734_, 1);
                                leanh::lean_inc_ref(v_resultType_3712_);
                                v___x_3736_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_3711_, v_resultType_3712_, v___f_3713_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
                                if leanh::lean_obj_tag(v___x_3736_) == 0 {
                                    v_a_3737_ = leanh::lean_ctor_get(v___x_3736_, 0);
                                    leanh::lean_inc(v_a_3737_);
                                    leanh::lean_dec_ref_known(v___x_3736_, 1);
                                    v_doBlockResultType_3738_ =
                                        leanh::lean_ctor_get(v___y_3716_, 3);
                                    leanh::lean_inc_ref(v_doBlockResultType_3738_);
                                    v___x_3739_ = l_Lean_Elab_Do_mkMonadApp(
                                        v_doBlockResultType_3738_,
                                        v___y_3716_,
                                        v___y_3717_,
                                        v___y_3718_,
                                        v___y_3719_,
                                        v___y_3720_,
                                        v___y_3721_,
                                        v___y_3722_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3739_) == 0 {
                                        v_a_3740_ = leanh::lean_ctor_get(v___x_3739_, 0);
                                        v_isSharedCheck_3753_ =
                                            (!leanh::lean_is_exclusive(v___x_3739_)) as u8;
                                        if v_isSharedCheck_3753_ == 0 {
                                            v___x_3742_ = v___x_3739_;
                                            v_isShared_3743_ = v_isSharedCheck_3753_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3740_);
                                            leanh::lean_dec(v___x_3739_);
                                            v___x_3742_ = leanh::lean_box(0);
                                            v_isShared_3743_ = v_isSharedCheck_3753_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_3737_);
                                        leanh::lean_dec(v_a_3735_);
                                        leanh::lean_dec(v_a_3725_);
                                        leanh::lean_dec(v_casesOnWrapper_3715_);
                                        leanh::lean_dec_ref(v_resultType_3712_);
                                        return v___x_3739_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3735_);
                                    leanh::lean_dec(v_a_3725_);
                                    leanh::lean_dec(v_casesOnWrapper_3715_);
                                    leanh::lean_dec_ref(v_resultType_3712_);
                                    return v___x_3736_;
                                }
                            } else {
                                leanh::lean_dec(v_a_3725_);
                                leanh::lean_dec(v_casesOnWrapper_3715_);
                                leanh::lean_dec_ref(v___f_3713_);
                                leanh::lean_dec_ref(v_resultType_3712_);
                                leanh::lean_dec(v_resultName_3711_);
                                return v___x_3734_;
                            }
                        } else {
                            leanh::lean_dec(v_a_3727_);
                            leanh::lean_dec(v_a_3725_);
                            leanh::lean_dec(v_casesOnWrapper_3715_);
                            leanh::lean_dec_ref(v___f_3713_);
                            leanh::lean_dec_ref(v_resultType_3712_);
                            leanh::lean_dec(v_resultName_3711_);
                            v_a_3754_ = leanh::lean_ctor_get(v___x_3729_, 0);
                            v_isSharedCheck_3761_ =
                                (!leanh::lean_is_exclusive(v___x_3729_)) as u8;
                            if v_isSharedCheck_3761_ == 0 {
                                v___x_3756_ = v___x_3729_;
                                v_isShared_3757_ = v_isSharedCheck_3761_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3754_);
                                leanh::lean_dec(v___x_3729_);
                                v___x_3756_ = leanh::lean_box(0);
                                v_isShared_3757_ = v_isSharedCheck_3761_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3725_);
                        leanh::lean_dec(v_casesOnWrapper_3715_);
                        leanh::lean_dec_ref(v___f_3713_);
                        leanh::lean_dec_ref(v_resultType_3712_);
                        leanh::lean_dec(v_resultName_3711_);
                        v_a_3762_ = leanh::lean_ctor_get(v___x_3726_, 0);
                        v_isSharedCheck_3769_ =
                            (!leanh::lean_is_exclusive(v___x_3726_)) as u8;
                        if v_isSharedCheck_3769_ == 0 {
                            v___x_3764_ = v___x_3726_;
                            v_isShared_3765_ = v_isSharedCheck_3769_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3762_);
                            leanh::lean_dec(v___x_3726_);
                            v___x_3764_ = leanh::lean_box(0);
                            v_isShared_3765_ = v_isSharedCheck_3769_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_casesOnWrapper_3715_);
                    leanh::lean_dec_ref(v___f_3713_);
                    leanh::lean_dec_ref(v_resultType_3712_);
                    leanh::lean_dec(v_resultName_3711_);
                    leanh::lean_dec_ref(v_getCont_3710_);
                    return v___x_3724_;
                }
            }
            1 => {
                v_u_3744_ = leanh::lean_ctor_get(v_baseMonadInfo_3714_, 1);
                v_v_3745_ = leanh::lean_ctor_get(v_baseMonadInfo_3714_, 2);
                leanh::lean_inc(v_v_3745_);
                v___x_3746_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3746_, 0, v_v_3745_);
                leanh::lean_ctor_set(v___x_3746_, 1, v___x_3732_);
                leanh::lean_inc(v_u_3744_);
                v___x_3747_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3747_, 0, v_u_3744_);
                leanh::lean_ctor_set(v___x_3747_, 1, v___x_3746_);
                v___x_3748_ = l_Lean_mkConst(v_casesOnWrapper_3715_, v___x_3747_);
                v___x_3749_ = l_Lean_mkApp5(
                    v___x_3748_,
                    v_resultType_3712_,
                    v_a_3740_,
                    v_a_3725_,
                    v_a_3735_,
                    v_a_3737_,
                );
                if v_isShared_3743_ == 0 {
                    leanh::lean_ctor_set(v___x_3742_, 0, v___x_3749_);
                    v___x_3751_ = v___x_3742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3752_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
                    v___x_3751_ = v_reuseFailAlloc_3752_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3751_;
            }
            3 => {
                if v_isShared_3757_ == 0 {
                    v___x_3759_ = v___x_3756_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
                    v___x_3759_ = v_reuseFailAlloc_3760_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3759_;
            }
            5 => {
                if v_isShared_3765_ == 0 {
                    v___x_3767_ = v___x_3764_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
                    v___x_3767_ = v_reuseFailAlloc_3768_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed(
    mut v_a_3770_: *mut leanh::LeanObject,
    mut v_getCont_3771_: *mut leanh::LeanObject,
    mut v_resultName_3772_: *mut leanh::LeanObject,
    mut v_resultType_3773_: *mut leanh::LeanObject,
    mut v___f_3774_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3775_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
    mut v___y_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3785_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4(
        v_a_3770_,
        v_getCont_3771_,
        v_resultName_3772_,
        v_resultType_3773_,
        v___f_3774_,
        v_baseMonadInfo_3775_,
        v_casesOnWrapper_3776_,
        v___y_3777_,
        v___y_3778_,
        v___y_3779_,
        v___y_3780_,
        v___y_3781_,
        v___y_3782_,
        v___y_3783_,
    );
    leanh::lean_dec(v___y_3783_);
    leanh::lean_dec_ref(v___y_3782_);
    leanh::lean_dec(v___y_3781_);
    leanh::lean_dec_ref(v___y_3780_);
    leanh::lean_dec(v___y_3779_);
    leanh::lean_dec_ref(v___y_3778_);
    leanh::lean_dec_ref(v___y_3777_);
    leanh::lean_dec_ref(v_baseMonadInfo_3775_);
    return v_res_3785_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__5(
    mut v_getCont_3789_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3790_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_3791_: *mut leanh::LeanObject,
    mut v_restoreCont_3792_: *mut leanh::LeanObject,
    mut v_dec_3793_: *mut leanh::LeanObject,
    mut v___y_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
    mut v___y_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
    mut v___y_3799_: *mut leanh::LeanObject,
    mut v___y_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultName_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___f_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3819_: u8 = 0;
    let mut v_a_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3823_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1;
                v___x_3803_ = l_Lean_Core_mkFreshUserName(v___x_3802_, v___y_3799_, v___y_3800_);
                if leanh::lean_obj_tag(v___x_3803_) == 0 {
                    v_a_3804_ = leanh::lean_ctor_get(v___x_3803_, 0);
                    leanh::lean_inc(v_a_3804_);
                    leanh::lean_dec_ref_known(v___x_3803_, 1);
                    v_resultName_3805_ = leanh::lean_ctor_get(v_dec_3793_, 0);
                    v_resultType_3806_ = leanh::lean_ctor_get(v_dec_3793_, 1);
                    v_k_3807_ = leanh::lean_ctor_get(v_dec_3793_, 2);
                    v_isSharedCheck_3819_ = (!leanh::lean_is_exclusive(v_dec_3793_)) as u8;
                    if v_isSharedCheck_3819_ == 0 {
                        v___x_3809_ = v_dec_3793_;
                        v_isShared_3810_ = v_isSharedCheck_3819_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3807_);
                        leanh::lean_inc(v_resultType_3806_);
                        leanh::lean_inc(v_resultName_3805_);
                        leanh::lean_dec(v_dec_3793_);
                        v___x_3809_ = leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3819_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_dec_3793_);
                    leanh::lean_dec_ref(v_restoreCont_3792_);
                    leanh::lean_dec(v_casesOnWrapper_3791_);
                    leanh::lean_dec_ref(v_baseMonadInfo_3790_);
                    leanh::lean_dec_ref(v_getCont_3789_);
                    v_a_3820_ = leanh::lean_ctor_get(v___x_3803_, 0);
                    v_isSharedCheck_3827_ = (!leanh::lean_is_exclusive(v___x_3803_)) as u8;
                    if v_isSharedCheck_3827_ == 0 {
                        v___x_3822_ = v___x_3803_;
                        v_isShared_3823_ = v_isSharedCheck_3827_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3820_);
                        leanh::lean_dec(v___x_3803_);
                        v___x_3822_ = leanh::lean_box(0);
                        v_isShared_3823_ = v_isSharedCheck_3827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_3811_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_optionT___lam__2___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                leanh::lean_closure_set(v___f_3811_, 0, v_k_3807_);
                leanh::lean_inc_ref(v_baseMonadInfo_3790_);
                leanh::lean_inc_ref(v_resultType_3806_);
                leanh::lean_inc(v_a_3804_);
                v___f_3812_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_optionT___lam__4___boxed as *mut core::ffi::c_void,
                    15,
                    7,
                );
                leanh::lean_closure_set(v___f_3812_, 0, v_a_3804_);
                leanh::lean_closure_set(v___f_3812_, 1, v_getCont_3789_);
                leanh::lean_closure_set(v___f_3812_, 2, v_resultName_3805_);
                leanh::lean_closure_set(v___f_3812_, 3, v_resultType_3806_);
                leanh::lean_closure_set(v___f_3812_, 4, v___f_3811_);
                leanh::lean_closure_set(v___f_3812_, 5, v_baseMonadInfo_3790_);
                leanh::lean_closure_set(v___f_3812_, 6, v_casesOnWrapper_3791_);
                v___x_3813_ =
                    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(
                        v_baseMonadInfo_3790_,
                        v_resultType_3806_,
                    );
                leanh::lean_dec_ref(v_baseMonadInfo_3790_);
                v___x_3814_ = 0;
                if v_isShared_3810_ == 0 {
                    leanh::lean_ctor_set(v___x_3809_, 2, v___f_3812_);
                    leanh::lean_ctor_set(v___x_3809_, 1, v___x_3813_);
                    leanh::lean_ctor_set(v___x_3809_, 0, v_a_3804_);
                    v___x_3816_ = v___x_3809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3818_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 1, v___x_3813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 2, v___f_3812_);
                    v___x_3816_ = v_reuseFailAlloc_3818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3816_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3814_,
                );
                leanh::lean_inc(v___y_3800_);
                leanh::lean_inc_ref(v___y_3799_);
                leanh::lean_inc(v___y_3798_);
                leanh::lean_inc_ref(v___y_3797_);
                leanh::lean_inc(v___y_3796_);
                leanh::lean_inc_ref(v___y_3795_);
                leanh::lean_inc_ref(v___y_3794_);
                v___x_3817_ = leanh::lean_apply_9(
                    v_restoreCont_3792_,
                    v___x_3816_,
                    v___y_3794_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                    v___y_3798_,
                    v___y_3799_,
                    v___y_3800_,
                    leanh::lean_box(0),
                );
                return v___x_3817_;
            }
            3 => {
                if v_isShared_3823_ == 0 {
                    v___x_3825_ = v___x_3822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3826_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
                    v___x_3825_ = v_reuseFailAlloc_3826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed(
    mut v_getCont_3828_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3829_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_3830_: *mut leanh::LeanObject,
    mut v_restoreCont_3831_: *mut leanh::LeanObject,
    mut v_dec_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
    mut v___y_3838_: *mut leanh::LeanObject,
    mut v___y_3839_: *mut leanh::LeanObject,
    mut v___y_3840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3841_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5(
        v_getCont_3828_,
        v_baseMonadInfo_3829_,
        v_casesOnWrapper_3830_,
        v_restoreCont_3831_,
        v_dec_3832_,
        v___y_3833_,
        v___y_3834_,
        v___y_3835_,
        v___y_3836_,
        v___y_3837_,
        v___y_3838_,
        v___y_3839_,
    );
    leanh::lean_dec(v___y_3839_);
    leanh::lean_dec_ref(v___y_3838_);
    leanh::lean_dec(v___y_3837_);
    leanh::lean_dec_ref(v___y_3836_);
    leanh::lean_dec(v___y_3835_);
    leanh::lean_dec_ref(v___y_3834_);
    leanh::lean_dec_ref(v___y_3833_);
    return v_res_3841_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__6(
    mut v_baseMonadInfo_3842_: *mut leanh::LeanObject,
    mut v_stM_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
    mut v___y_3846_: *mut leanh::LeanObject,
    mut v___y_3847_: *mut leanh::LeanObject,
    mut v___y_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
    mut v___y_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM(
        v_baseMonadInfo_3842_,
        v___y_3844_,
    );
    leanh::lean_inc(v___y_3851_);
    leanh::lean_inc_ref(v___y_3850_);
    leanh::lean_inc(v___y_3849_);
    leanh::lean_inc_ref(v___y_3848_);
    leanh::lean_inc(v___y_3847_);
    leanh::lean_inc_ref(v___y_3846_);
    leanh::lean_inc_ref(v___y_3845_);
    v___x_3854_ = leanh::lean_apply_9(
        v_stM_3843_,
        v___x_3853_,
        v___y_3845_,
        v___y_3846_,
        v___y_3847_,
        v___y_3848_,
        v___y_3849_,
        v___y_3850_,
        v___y_3851_,
        leanh::lean_box(0),
    );
    return v___x_3854_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed(
    mut v_baseMonadInfo_3855_: *mut leanh::LeanObject,
    mut v_stM_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
    mut v___y_3862_: *mut leanh::LeanObject,
    mut v___y_3863_: *mut leanh::LeanObject,
    mut v___y_3864_: *mut leanh::LeanObject,
    mut v___y_3865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3866_ = l_Lean_Elab_Do_ControlStack_optionT___lam__6(
        v_baseMonadInfo_3855_,
        v_stM_3856_,
        v___y_3857_,
        v___y_3858_,
        v___y_3859_,
        v___y_3860_,
        v___y_3861_,
        v___y_3862_,
        v___y_3863_,
        v___y_3864_,
    );
    leanh::lean_dec(v___y_3864_);
    leanh::lean_dec_ref(v___y_3863_);
    leanh::lean_dec(v___y_3862_);
    leanh::lean_dec_ref(v___y_3861_);
    leanh::lean_dec(v___y_3860_);
    leanh::lean_dec_ref(v___y_3859_);
    leanh::lean_dec_ref(v___y_3858_);
    leanh::lean_dec_ref(v_baseMonadInfo_3855_);
    return v_res_3866_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__7(
    mut v_m_3867_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3868_: *mut leanh::LeanObject,
    mut v_optionTWrapper_3869_: *mut leanh::LeanObject,
    mut v___y_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
    mut v___y_3874_: *mut leanh::LeanObject,
    mut v___y_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v_u_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3876_);
                leanh::lean_inc_ref(v___y_3875_);
                leanh::lean_inc(v___y_3874_);
                leanh::lean_inc_ref(v___y_3873_);
                leanh::lean_inc(v___y_3872_);
                leanh::lean_inc_ref(v___y_3871_);
                leanh::lean_inc_ref(v___y_3870_);
                v___x_3878_ = leanh::lean_apply_8(
                    v_m_3867_,
                    v___y_3870_,
                    v___y_3871_,
                    v___y_3872_,
                    v___y_3873_,
                    v___y_3874_,
                    v___y_3875_,
                    v___y_3876_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3878_) == 0 {
                    v_a_3879_ = leanh::lean_ctor_get(v___x_3878_, 0);
                    v_isSharedCheck_3893_ = (!leanh::lean_is_exclusive(v___x_3878_)) as u8;
                    if v_isSharedCheck_3893_ == 0 {
                        v___x_3881_ = v___x_3878_;
                        v_isShared_3882_ = v_isSharedCheck_3893_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3879_);
                        leanh::lean_dec(v___x_3878_);
                        v___x_3881_ = leanh::lean_box(0);
                        v_isShared_3882_ = v_isSharedCheck_3893_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_optionTWrapper_3869_);
                    return v___x_3878_;
                }
            }
            1 => {
                v_u_3883_ = leanh::lean_ctor_get(v_baseMonadInfo_3868_, 1);
                v_v_3884_ = leanh::lean_ctor_get(v_baseMonadInfo_3868_, 2);
                v___x_3885_ = leanh::lean_box(0);
                leanh::lean_inc(v_v_3884_);
                v___x_3886_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3886_, 0, v_v_3884_);
                leanh::lean_ctor_set(v___x_3886_, 1, v___x_3885_);
                leanh::lean_inc(v_u_3883_);
                v___x_3887_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3887_, 0, v_u_3883_);
                leanh::lean_ctor_set(v___x_3887_, 1, v___x_3886_);
                v___x_3888_ = l_Lean_mkConst(v_optionTWrapper_3869_, v___x_3887_);
                v___x_3889_ = l_Lean_Expr_app___override(v___x_3888_, v_a_3879_);
                if v_isShared_3882_ == 0 {
                    leanh::lean_ctor_set(v___x_3881_, 0, v___x_3889_);
                    v___x_3891_ = v___x_3881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3892_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3889_);
                    v___x_3891_ = v_reuseFailAlloc_3892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed(
    mut v_m_3894_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_3895_: *mut leanh::LeanObject,
    mut v_optionTWrapper_3896_: *mut leanh::LeanObject,
    mut v___y_3897_: *mut leanh::LeanObject,
    mut v___y_3898_: *mut leanh::LeanObject,
    mut v___y_3899_: *mut leanh::LeanObject,
    mut v___y_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3905_ = l_Lean_Elab_Do_ControlStack_optionT___lam__7(
        v_m_3894_,
        v_baseMonadInfo_3895_,
        v_optionTWrapper_3896_,
        v___y_3897_,
        v___y_3898_,
        v___y_3899_,
        v___y_3900_,
        v___y_3901_,
        v___y_3902_,
        v___y_3903_,
    );
    leanh::lean_dec(v___y_3903_);
    leanh::lean_dec_ref(v___y_3902_);
    leanh::lean_dec(v___y_3901_);
    leanh::lean_dec_ref(v___y_3900_);
    leanh::lean_dec(v___y_3899_);
    leanh::lean_dec_ref(v___y_3898_);
    leanh::lean_dec_ref(v___y_3897_);
    leanh::lean_dec_ref(v_baseMonadInfo_3895_);
    return v_res_3905_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_optionT(
    mut v_baseMonadInfo_3906_: *mut leanh::LeanObject,
    mut v_optionTWrapper_3907_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_3908_: *mut leanh::LeanObject,
    mut v_getCont_3909_: *mut leanh::LeanObject,
    mut v_base_3910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_description_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stM_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_runInBase_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreCont_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___f_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_description_3911_ = leanh::lean_ctor_get(v_base_3910_, 0);
                v_m_3912_ = leanh::lean_ctor_get(v_base_3910_, 1);
                v_stM_3913_ = leanh::lean_ctor_get(v_base_3910_, 2);
                v_runInBase_3914_ = leanh::lean_ctor_get(v_base_3910_, 3);
                v_restoreCont_3915_ = leanh::lean_ctor_get(v_base_3910_, 4);
                v_isSharedCheck_3927_ = (!leanh::lean_is_exclusive(v_base_3910_)) as u8;
                if v_isSharedCheck_3927_ == 0 {
                    v___x_3917_ = v_base_3910_;
                    v_isShared_3918_ = v_isSharedCheck_3927_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_restoreCont_3915_);
                    leanh::lean_inc(v_runInBase_3914_);
                    leanh::lean_inc(v_stM_3913_);
                    leanh::lean_inc(v_m_3912_);
                    leanh::lean_inc(v_description_3911_);
                    leanh::lean_dec(v_base_3910_);
                    v___x_3917_ = leanh::lean_box(0);
                    v_isShared_3918_ = v_isSharedCheck_3927_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3919_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_optionT___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                leanh::lean_closure_set(v___f_3919_, 0, v_runInBase_3914_);
                v___f_3920_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_optionT___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3920_, 0, v_description_3911_);
                leanh::lean_inc_ref_n(v_baseMonadInfo_3906_, 2);
                v___f_3921_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_optionT___lam__5___boxed as *mut core::ffi::c_void,
                    13,
                    4,
                );
                leanh::lean_closure_set(v___f_3921_, 0, v_getCont_3909_);
                leanh::lean_closure_set(v___f_3921_, 1, v_baseMonadInfo_3906_);
                leanh::lean_closure_set(v___f_3921_, 2, v_casesOnWrapper_3908_);
                leanh::lean_closure_set(v___f_3921_, 3, v_restoreCont_3915_);
                v___f_3922_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_optionT___lam__6___boxed as *mut core::ffi::c_void,
                    11,
                    2,
                );
                leanh::lean_closure_set(v___f_3922_, 0, v_baseMonadInfo_3906_);
                leanh::lean_closure_set(v___f_3922_, 1, v_stM_3913_);
                v___f_3923_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_optionT___lam__7___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                leanh::lean_closure_set(v___f_3923_, 0, v_m_3912_);
                leanh::lean_closure_set(v___f_3923_, 1, v_baseMonadInfo_3906_);
                leanh::lean_closure_set(v___f_3923_, 2, v_optionTWrapper_3907_);
                if v_isShared_3918_ == 0 {
                    leanh::lean_ctor_set(v___x_3917_, 4, v___f_3921_);
                    leanh::lean_ctor_set(v___x_3917_, 3, v___f_3919_);
                    leanh::lean_ctor_set(v___x_3917_, 2, v___f_3922_);
                    leanh::lean_ctor_set(v___x_3917_, 1, v___f_3923_);
                    leanh::lean_ctor_set(v___x_3917_, 0, v___f_3920_);
                    v___x_3925_ = v___x_3917_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___f_3920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 1, v___f_3923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 2, v___f_3922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 3, v___f_3919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 4, v___f_3921_);
                    v___x_3925_ = v_reuseFailAlloc_3926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(
    mut v_00_u03b1_3928_: *mut leanh::LeanObject,
    mut v_name_3929_: *mut leanh::LeanObject,
    mut v_bi_3930_: u8,
    mut v_type_3931_: *mut leanh::LeanObject,
    mut v_k_3932_: *mut leanh::LeanObject,
    mut v_kind_3933_: u8,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
    mut v___y_3938_: *mut leanh::LeanObject,
    mut v___y_3939_: *mut leanh::LeanObject,
    mut v___y_3940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___redArg(v_name_3929_, v_bi_3930_, v_type_3931_, v_k_3932_, v_kind_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
    return v___x_3942_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0___boxed(
    mut v_00_u03b1_3943_: *mut leanh::LeanObject,
    mut v_name_3944_: *mut leanh::LeanObject,
    mut v_bi_3945_: *mut leanh::LeanObject,
    mut v_type_3946_: *mut leanh::LeanObject,
    mut v_k_3947_: *mut leanh::LeanObject,
    mut v_kind_3948_: *mut leanh::LeanObject,
    mut v___y_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3957_: u8 = 0;
    let mut v_kind_boxed_3958_: u8 = 0;
    let mut v_res_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3957_ = (leanh::lean_unbox(v_bi_3945_) as u8);
    v_kind_boxed_3958_ = (leanh::lean_unbox(v_kind_3948_) as u8);
    v_res_3959_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0_spec__0(v_00_u03b1_3943_, v_name_3944_, v_bi_boxed_3957_, v_type_3946_, v_k_3947_, v_kind_boxed_3958_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    leanh::lean_dec(v___y_3955_);
    leanh::lean_dec_ref(v___y_3954_);
    leanh::lean_dec(v___y_3953_);
    leanh::lean_dec_ref(v___y_3952_);
    leanh::lean_dec(v___y_3951_);
    leanh::lean_dec_ref(v___y_3950_);
    leanh::lean_dec_ref(v___y_3949_);
    return v_res_3959_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(
    mut v_00_u03b1_3960_: *mut leanh::LeanObject,
    mut v_name_3961_: *mut leanh::LeanObject,
    mut v_type_3962_: *mut leanh::LeanObject,
    mut v_k_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
    mut v___y_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(
            v_name_3961_,
            v_type_3962_,
            v_k_3963_,
            v___y_3964_,
            v___y_3965_,
            v___y_3966_,
            v___y_3967_,
            v___y_3968_,
            v___y_3969_,
            v___y_3970_,
        );
    return v___x_3972_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___boxed(
    mut v_00_u03b1_3973_: *mut leanh::LeanObject,
    mut v_name_3974_: *mut leanh::LeanObject,
    mut v_type_3975_: *mut leanh::LeanObject,
    mut v_k_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3985_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0(
        v_00_u03b1_3973_,
        v_name_3974_,
        v_type_3975_,
        v_k_3976_,
        v___y_3977_,
        v___y_3978_,
        v___y_3979_,
        v___y_3980_,
        v___y_3981_,
        v___y_3982_,
        v___y_3983_,
    );
    leanh::lean_dec(v___y_3983_);
    leanh::lean_dec_ref(v___y_3982_);
    leanh::lean_dec(v___y_3981_);
    leanh::lean_dec_ref(v___y_3980_);
    leanh::lean_dec(v___y_3979_);
    leanh::lean_dec_ref(v___y_3978_);
    leanh::lean_dec_ref(v___y_3977_);
    return v_res_3985_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(
    mut v_baseMonadInfo_3989_: *mut leanh::LeanObject,
    mut v_getCont_3990_: *mut leanh::LeanObject,
    mut v_00_u03b1_3991_: *mut leanh::LeanObject,
    mut v_a_3992_: *mut leanh::LeanObject,
    mut v_a_3993_: *mut leanh::LeanObject,
    mut v_a_3994_: *mut leanh::LeanObject,
    mut v_a_3995_: *mut leanh::LeanObject,
    mut v_a_3996_: *mut leanh::LeanObject,
    mut v_a_3997_: *mut leanh::LeanObject,
    mut v_a_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v_u_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4009_: u8 = 0;
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4021_: u8 = 0;
    let mut v_unused_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut v_a_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_3998_);
                leanh::lean_inc_ref(v_a_3997_);
                leanh::lean_inc(v_a_3996_);
                leanh::lean_inc_ref(v_a_3995_);
                leanh::lean_inc(v_a_3994_);
                leanh::lean_inc_ref(v_a_3993_);
                leanh::lean_inc_ref(v_a_3992_);
                v___x_4000_ = leanh::lean_apply_8(
                    v_getCont_3990_,
                    v_a_3992_,
                    v_a_3993_,
                    v_a_3994_,
                    v_a_3995_,
                    v_a_3996_,
                    v_a_3997_,
                    v_a_3998_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4000_) == 0 {
                    v_a_4001_ = leanh::lean_ctor_get(v___x_4000_, 0);
                    v_isSharedCheck_4023_ = (!leanh::lean_is_exclusive(v___x_4000_)) as u8;
                    if v_isSharedCheck_4023_ == 0 {
                        v___x_4003_ = v___x_4000_;
                        v_isShared_4004_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4001_);
                        leanh::lean_dec(v___x_4000_);
                        v___x_4003_ = leanh::lean_box(0);
                        v_isShared_4004_ = v_isSharedCheck_4023_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_00_u03b1_3991_);
                    v_a_4024_ = leanh::lean_ctor_get(v___x_4000_, 0);
                    v_isSharedCheck_4031_ = (!leanh::lean_is_exclusive(v___x_4000_)) as u8;
                    if v_isSharedCheck_4031_ == 0 {
                        v___x_4026_ = v___x_4000_;
                        v_isShared_4027_ = v_isSharedCheck_4031_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4024_);
                        leanh::lean_dec(v___x_4000_);
                        v___x_4026_ = leanh::lean_box(0);
                        v_isShared_4027_ = v_isSharedCheck_4031_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_u_4005_ = leanh::lean_ctor_get(v_baseMonadInfo_3989_, 1);
                v_resultType_4006_ = leanh::lean_ctor_get(v_a_4001_, 0);
                v_isSharedCheck_4021_ = (!leanh::lean_is_exclusive(v_a_4001_)) as u8;
                if v_isSharedCheck_4021_ == 0 {
                    v_unused_4022_ = leanh::lean_ctor_get(v_a_4001_, 1);
                    leanh::lean_dec(v_unused_4022_);
                    v___x_4008_ = v_a_4001_;
                    v_isShared_4009_ = v_isSharedCheck_4021_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_resultType_4006_);
                    leanh::lean_dec(v_a_4001_);
                    v___x_4008_ = leanh::lean_box(0);
                    v_isShared_4009_ = v_isSharedCheck_4021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4010_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_4005_);
                if v_isShared_4009_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4008_, 1);
                    leanh::lean_ctor_set(v___x_4008_, 1, v___x_4010_);
                    leanh::lean_ctor_set(v___x_4008_, 0, v_u_4005_);
                    v___x_4012_ = v___x_4008_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4020_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_u_4005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4020_, 1, v___x_4010_);
                    v___x_4012_ = v_reuseFailAlloc_4020_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4013_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1;
                leanh::lean_inc(v_u_4005_);
                v___x_4014_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4014_, 0, v_u_4005_);
                leanh::lean_ctor_set(v___x_4014_, 1, v___x_4012_);
                v___x_4015_ = l_Lean_mkConst(v___x_4013_, v___x_4014_);
                v___x_4016_ = l_Lean_mkAppB(v___x_4015_, v_resultType_4006_, v_00_u03b1_3991_);
                if v_isShared_4004_ == 0 {
                    leanh::lean_ctor_set(v___x_4003_, 0, v___x_4016_);
                    v___x_4018_ = v___x_4003_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4018_;
            }
            5 => {
                if v_isShared_4027_ == 0 {
                    v___x_4029_ = v___x_4026_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4030_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
                    v___x_4029_ = v_reuseFailAlloc_4030_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___boxed(
    mut v_baseMonadInfo_4032_: *mut leanh::LeanObject,
    mut v_getCont_4033_: *mut leanh::LeanObject,
    mut v_00_u03b1_4034_: *mut leanh::LeanObject,
    mut v_a_4035_: *mut leanh::LeanObject,
    mut v_a_4036_: *mut leanh::LeanObject,
    mut v_a_4037_: *mut leanh::LeanObject,
    mut v_a_4038_: *mut leanh::LeanObject,
    mut v_a_4039_: *mut leanh::LeanObject,
    mut v_a_4040_: *mut leanh::LeanObject,
    mut v_a_4041_: *mut leanh::LeanObject,
    mut v_a_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4043_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(
        v_baseMonadInfo_4032_,
        v_getCont_4033_,
        v_00_u03b1_4034_,
        v_a_4035_,
        v_a_4036_,
        v_a_4037_,
        v_a_4038_,
        v_a_4039_,
        v_a_4040_,
        v_a_4041_,
    );
    leanh::lean_dec(v_a_4041_);
    leanh::lean_dec_ref(v_a_4040_);
    leanh::lean_dec(v_a_4039_);
    leanh::lean_dec_ref(v_a_4038_);
    leanh::lean_dec(v_a_4037_);
    leanh::lean_dec_ref(v_a_4036_);
    leanh::lean_dec_ref(v_a_4035_);
    leanh::lean_dec_ref(v_baseMonadInfo_4032_);
    return v_res_4043_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__0(
    mut v_k_4044_: *mut leanh::LeanObject,
    mut v_r_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: u8 = 0;
    let mut v___x_4060_: u8 = 0;
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4068_: u8 = 0;
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4073_: u8 = 0;
    let mut v_a_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_a_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4085_: u8 = 0;
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4089_: u8 = 0;
    let mut v_a_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_4052_);
                leanh::lean_inc_ref(v___y_4051_);
                leanh::lean_inc(v___y_4050_);
                leanh::lean_inc_ref(v___y_4049_);
                leanh::lean_inc(v___y_4048_);
                leanh::lean_inc_ref(v___y_4047_);
                leanh::lean_inc_ref(v___y_4046_);
                v___x_4054_ = leanh::lean_apply_8(
                    v_k_4044_,
                    v___y_4046_,
                    v___y_4047_,
                    v___y_4048_,
                    v___y_4049_,
                    v___y_4050_,
                    v___y_4051_,
                    v___y_4052_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4054_) == 0 {
                    v_a_4055_ = leanh::lean_ctor_get(v___x_4054_, 0);
                    leanh::lean_inc_n(v_a_4055_, 2);
                    leanh::lean_dec_ref_known(v___x_4054_, 1);
                    v___x_4056_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4057_ = lean_mk_empty_array_with_capacity(v___x_4056_);
                    v___x_4058_ = lean_array_push(v___x_4057_, v_r_4045_);
                    v___x_4059_ = 0;
                    v___x_4060_ = 1;
                    v___x_4061_ = 1;
                    v___x_4062_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_4058_,
                        v_a_4055_,
                        v___x_4059_,
                        v___x_4060_,
                        v___x_4059_,
                        v___x_4060_,
                        v___x_4061_,
                        v___y_4049_,
                        v___y_4050_,
                        v___y_4051_,
                        v___y_4052_,
                    );
                    leanh::lean_dec_ref(v___x_4058_);
                    if leanh::lean_obj_tag(v___x_4062_) == 0 {
                        v_a_4063_ = leanh::lean_ctor_get(v___x_4062_, 0);
                        leanh::lean_inc(v_a_4063_);
                        leanh::lean_dec_ref_known(v___x_4062_, 1);
                        leanh::lean_inc(v___y_4052_);
                        leanh::lean_inc_ref(v___y_4051_);
                        leanh::lean_inc(v___y_4050_);
                        leanh::lean_inc_ref(v___y_4049_);
                        v___x_4064_ = lean_infer_type(
                            v_a_4055_,
                            v___y_4049_,
                            v___y_4050_,
                            v___y_4051_,
                            v___y_4052_,
                        );
                        if leanh::lean_obj_tag(v___x_4064_) == 0 {
                            v_a_4065_ = leanh::lean_ctor_get(v___x_4064_, 0);
                            v_isSharedCheck_4073_ =
                                (!leanh::lean_is_exclusive(v___x_4064_)) as u8;
                            if v_isSharedCheck_4073_ == 0 {
                                v___x_4067_ = v___x_4064_;
                                v_isShared_4068_ = v_isSharedCheck_4073_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4065_);
                                leanh::lean_dec(v___x_4064_);
                                v___x_4067_ = leanh::lean_box(0);
                                v_isShared_4068_ = v_isSharedCheck_4073_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4063_);
                            v_a_4074_ = leanh::lean_ctor_get(v___x_4064_, 0);
                            v_isSharedCheck_4081_ =
                                (!leanh::lean_is_exclusive(v___x_4064_)) as u8;
                            if v_isSharedCheck_4081_ == 0 {
                                v___x_4076_ = v___x_4064_;
                                v_isShared_4077_ = v_isSharedCheck_4081_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4074_);
                                leanh::lean_dec(v___x_4064_);
                                v___x_4076_ = leanh::lean_box(0);
                                v_isShared_4077_ = v_isSharedCheck_4081_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4055_);
                        v_a_4082_ = leanh::lean_ctor_get(v___x_4062_, 0);
                        v_isSharedCheck_4089_ =
                            (!leanh::lean_is_exclusive(v___x_4062_)) as u8;
                        if v_isSharedCheck_4089_ == 0 {
                            v___x_4084_ = v___x_4062_;
                            v_isShared_4085_ = v_isSharedCheck_4089_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4082_);
                            leanh::lean_dec(v___x_4062_);
                            v___x_4084_ = leanh::lean_box(0);
                            v_isShared_4085_ = v_isSharedCheck_4089_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_r_4045_);
                    v_a_4090_ = leanh::lean_ctor_get(v___x_4054_, 0);
                    v_isSharedCheck_4097_ = (!leanh::lean_is_exclusive(v___x_4054_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4092_ = v___x_4054_;
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4090_);
                        leanh::lean_dec(v___x_4054_);
                        v___x_4092_ = leanh::lean_box(0);
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4069_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4069_, 0, v_a_4063_);
                leanh::lean_ctor_set(v___x_4069_, 1, v_a_4065_);
                if v_isShared_4068_ == 0 {
                    leanh::lean_ctor_set(v___x_4067_, 0, v___x_4069_);
                    v___x_4071_ = v___x_4067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4069_);
                    v___x_4071_ = v_reuseFailAlloc_4072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4071_;
            }
            3 => {
                if v_isShared_4077_ == 0 {
                    v___x_4079_ = v___x_4076_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4080_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
                    v___x_4079_ = v_reuseFailAlloc_4080_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4079_;
            }
            5 => {
                if v_isShared_4085_ == 0 {
                    v___x_4087_ = v___x_4084_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
                    v___x_4087_ = v_reuseFailAlloc_4088_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4087_;
            }
            7 => {
                if v_isShared_4093_ == 0 {
                    v___x_4095_ = v___x_4092_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed(
    mut v_k_4098_: *mut leanh::LeanObject,
    mut v_r_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
    mut v___y_4101_: *mut leanh::LeanObject,
    mut v___y_4102_: *mut leanh::LeanObject,
    mut v___y_4103_: *mut leanh::LeanObject,
    mut v___y_4104_: *mut leanh::LeanObject,
    mut v___y_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4108_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__0(
        v_k_4098_,
        v_r_4099_,
        v___y_4100_,
        v___y_4101_,
        v___y_4102_,
        v___y_4103_,
        v___y_4104_,
        v___y_4105_,
        v___y_4106_,
    );
    leanh::lean_dec(v___y_4106_);
    leanh::lean_dec_ref(v___y_4105_);
    leanh::lean_dec(v___y_4104_);
    leanh::lean_dec_ref(v___y_4103_);
    leanh::lean_dec(v___y_4102_);
    leanh::lean_dec_ref(v___y_4101_);
    leanh::lean_dec_ref(v___y_4100_);
    return v_res_4108_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__1(
    mut v_k_4109_: *mut leanh::LeanObject,
    mut v_r_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
    mut v___y_4116_: *mut leanh::LeanObject,
    mut v___y_4117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4117_);
    leanh::lean_inc_ref(v___y_4116_);
    leanh::lean_inc(v___y_4115_);
    leanh::lean_inc_ref(v___y_4114_);
    leanh::lean_inc(v___y_4113_);
    leanh::lean_inc_ref(v___y_4112_);
    leanh::lean_inc_ref(v___y_4111_);
    leanh::lean_inc_ref(v_r_4110_);
    v___x_4119_ = leanh::lean_apply_9(
        v_k_4109_,
        v_r_4110_,
        v___y_4111_,
        v___y_4112_,
        v___y_4113_,
        v___y_4114_,
        v___y_4115_,
        v___y_4116_,
        v___y_4117_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_4119_) == 0 {
        let mut v_a_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4124_: u8 = 0;
        let mut v___x_4125_: u8 = 0;
        let mut v___x_4126_: u8 = 0;
        let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4120_ = leanh::lean_ctor_get(v___x_4119_, 0);
        leanh::lean_inc(v_a_4120_);
        leanh::lean_dec_ref_known(v___x_4119_, 1);
        v___x_4121_ = leanh::lean_unsigned_to_nat(1);
        v___x_4122_ = lean_mk_empty_array_with_capacity(v___x_4121_);
        v___x_4123_ = lean_array_push(v___x_4122_, v_r_4110_);
        v___x_4124_ = 0;
        v___x_4125_ = 1;
        v___x_4126_ = 1;
        v___x_4127_ = l_Lean_Meta_mkLambdaFVars(
            v___x_4123_,
            v_a_4120_,
            v___x_4124_,
            v___x_4125_,
            v___x_4124_,
            v___x_4125_,
            v___x_4126_,
            v___y_4114_,
            v___y_4115_,
            v___y_4116_,
            v___y_4117_,
        );
        leanh::lean_dec_ref(v___x_4123_);
        return v___x_4127_;
    } else {
        leanh::lean_dec_ref(v_r_4110_);
        return v___x_4119_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed(
    mut v_k_4128_: *mut leanh::LeanObject,
    mut v_r_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4138_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__1(
        v_k_4128_,
        v_r_4129_,
        v___y_4130_,
        v___y_4131_,
        v___y_4132_,
        v___y_4133_,
        v___y_4134_,
        v___y_4135_,
        v___y_4136_,
    );
    leanh::lean_dec(v___y_4136_);
    leanh::lean_dec_ref(v___y_4135_);
    leanh::lean_dec(v___y_4134_);
    leanh::lean_dec_ref(v___y_4133_);
    leanh::lean_dec(v___y_4132_);
    leanh::lean_dec_ref(v___y_4131_);
    leanh::lean_dec_ref(v___y_4130_);
    return v_res_4138_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__2(
    mut v_a_4139_: *mut leanh::LeanObject,
    mut v_getCont_4140_: *mut leanh::LeanObject,
    mut v_resultName_4141_: *mut leanh::LeanObject,
    mut v_resultType_4142_: *mut leanh::LeanObject,
    mut v___f_4143_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_4144_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_4145_: *mut leanh::LeanObject,
    mut v_00_u03b5_4146_: *mut leanh::LeanObject,
    mut v___y_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
    mut v___y_4150_: *mut leanh::LeanObject,
    mut v___y_4151_: *mut leanh::LeanObject,
    mut v___y_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4166_: u8 = 0;
    let mut v___f_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4174_: u8 = 0;
    let mut v_fst_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v_u_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut v_a_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_a_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4155_ = l_Lean_Meta_getFVarFromUserName(
                    v_a_4139_,
                    v___y_4150_,
                    v___y_4151_,
                    v___y_4152_,
                    v___y_4153_,
                );
                if leanh::lean_obj_tag(v___x_4155_) == 0 {
                    v_a_4156_ = leanh::lean_ctor_get(v___x_4155_, 0);
                    leanh::lean_inc(v_a_4156_);
                    leanh::lean_dec_ref_known(v___x_4155_, 1);
                    leanh::lean_inc(v___y_4153_);
                    leanh::lean_inc_ref(v___y_4152_);
                    leanh::lean_inc(v___y_4151_);
                    leanh::lean_inc_ref(v___y_4150_);
                    leanh::lean_inc(v___y_4149_);
                    leanh::lean_inc_ref(v___y_4148_);
                    leanh::lean_inc_ref(v___y_4147_);
                    v___x_4157_ = leanh::lean_apply_8(
                        v_getCont_4140_,
                        v___y_4147_,
                        v___y_4148_,
                        v___y_4149_,
                        v___y_4150_,
                        v___y_4151_,
                        v___y_4152_,
                        v___y_4153_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4157_) == 0 {
                        v_a_4158_ = leanh::lean_ctor_get(v___x_4157_, 0);
                        leanh::lean_inc(v_a_4158_);
                        leanh::lean_dec_ref_known(v___x_4157_, 1);
                        v___x_4159_ = l_Lean_Elab_Do_ControlStack_optionT___lam__4___closed__1;
                        v___x_4160_ =
                            l_Lean_Core_mkFreshUserName(v___x_4159_, v___y_4152_, v___y_4153_);
                        if leanh::lean_obj_tag(v___x_4160_) == 0 {
                            v_a_4161_ = leanh::lean_ctor_get(v___x_4160_, 0);
                            leanh::lean_inc(v_a_4161_);
                            leanh::lean_dec_ref_known(v___x_4160_, 1);
                            v_resultType_4162_ = leanh::lean_ctor_get(v_a_4158_, 0);
                            v_k_4163_ = leanh::lean_ctor_get(v_a_4158_, 1);
                            v_isSharedCheck_4204_ =
                                (!leanh::lean_is_exclusive(v_a_4158_)) as u8;
                            if v_isSharedCheck_4204_ == 0 {
                                v___x_4165_ = v_a_4158_;
                                v_isShared_4166_ = v_isSharedCheck_4204_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_k_4163_);
                                leanh::lean_inc(v_resultType_4162_);
                                leanh::lean_dec(v_a_4158_);
                                v___x_4165_ = leanh::lean_box(0);
                                v_isShared_4166_ = v_isSharedCheck_4204_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4158_);
                            leanh::lean_dec(v_a_4156_);
                            leanh::lean_dec_ref(v_00_u03b5_4146_);
                            leanh::lean_dec(v_casesOnWrapper_4145_);
                            leanh::lean_dec_ref(v___f_4143_);
                            leanh::lean_dec_ref(v_resultType_4142_);
                            leanh::lean_dec(v_resultName_4141_);
                            v_a_4205_ = leanh::lean_ctor_get(v___x_4160_, 0);
                            v_isSharedCheck_4212_ =
                                (!leanh::lean_is_exclusive(v___x_4160_)) as u8;
                            if v_isSharedCheck_4212_ == 0 {
                                v___x_4207_ = v___x_4160_;
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4205_);
                                leanh::lean_dec(v___x_4160_);
                                v___x_4207_ = leanh::lean_box(0);
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4156_);
                        leanh::lean_dec_ref(v_00_u03b5_4146_);
                        leanh::lean_dec(v_casesOnWrapper_4145_);
                        leanh::lean_dec_ref(v___f_4143_);
                        leanh::lean_dec_ref(v_resultType_4142_);
                        leanh::lean_dec(v_resultName_4141_);
                        v_a_4213_ = leanh::lean_ctor_get(v___x_4157_, 0);
                        v_isSharedCheck_4220_ =
                            (!leanh::lean_is_exclusive(v___x_4157_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v___x_4215_ = v___x_4157_;
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4213_);
                            leanh::lean_dec(v___x_4157_);
                            v___x_4215_ = leanh::lean_box(0);
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_00_u03b5_4146_);
                    leanh::lean_dec(v_casesOnWrapper_4145_);
                    leanh::lean_dec_ref(v___f_4143_);
                    leanh::lean_dec_ref(v_resultType_4142_);
                    leanh::lean_dec(v_resultName_4141_);
                    leanh::lean_dec_ref(v_getCont_4140_);
                    return v___x_4155_;
                }
            }
            1 => {
                v___f_4167_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_exceptT___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                leanh::lean_closure_set(v___f_4167_, 0, v_k_4163_);
                v___x_4168_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_a_4161_, v_resultType_4162_, v___f_4167_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
                if leanh::lean_obj_tag(v___x_4168_) == 0 {
                    v_a_4169_ = leanh::lean_ctor_get(v___x_4168_, 0);
                    leanh::lean_inc(v_a_4169_);
                    leanh::lean_dec_ref_known(v___x_4168_, 1);
                    leanh::lean_inc_ref(v_resultType_4142_);
                    v___x_4170_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_ControlStack_optionT_spec__0___redArg(v_resultName_4141_, v_resultType_4142_, v___f_4143_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
                    if leanh::lean_obj_tag(v___x_4170_) == 0 {
                        v_a_4171_ = leanh::lean_ctor_get(v___x_4170_, 0);
                        v_isSharedCheck_4195_ =
                            (!leanh::lean_is_exclusive(v___x_4170_)) as u8;
                        if v_isSharedCheck_4195_ == 0 {
                            v___x_4173_ = v___x_4170_;
                            v_isShared_4174_ = v_isSharedCheck_4195_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4171_);
                            leanh::lean_dec(v___x_4170_);
                            v___x_4173_ = leanh::lean_box(0);
                            v_isShared_4174_ = v_isSharedCheck_4195_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4169_);
                        leanh::lean_del_object(v___x_4165_);
                        leanh::lean_dec(v_a_4156_);
                        leanh::lean_dec_ref(v_00_u03b5_4146_);
                        leanh::lean_dec(v_casesOnWrapper_4145_);
                        leanh::lean_dec_ref(v_resultType_4142_);
                        v_a_4196_ = leanh::lean_ctor_get(v___x_4170_, 0);
                        v_isSharedCheck_4203_ =
                            (!leanh::lean_is_exclusive(v___x_4170_)) as u8;
                        if v_isSharedCheck_4203_ == 0 {
                            v___x_4198_ = v___x_4170_;
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4196_);
                            leanh::lean_dec(v___x_4170_);
                            v___x_4198_ = leanh::lean_box(0);
                            v_isShared_4199_ = v_isSharedCheck_4203_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4165_);
                    leanh::lean_dec(v_a_4156_);
                    leanh::lean_dec_ref(v_00_u03b5_4146_);
                    leanh::lean_dec(v_casesOnWrapper_4145_);
                    leanh::lean_dec_ref(v___f_4143_);
                    leanh::lean_dec_ref(v_resultType_4142_);
                    leanh::lean_dec(v_resultName_4141_);
                    return v___x_4168_;
                }
            }
            2 => {
                v_fst_4175_ = leanh::lean_ctor_get(v_a_4171_, 0);
                v_snd_4176_ = leanh::lean_ctor_get(v_a_4171_, 1);
                v_isSharedCheck_4194_ = (!leanh::lean_is_exclusive(v_a_4171_)) as u8;
                if v_isSharedCheck_4194_ == 0 {
                    v___x_4178_ = v_a_4171_;
                    v_isShared_4179_ = v_isSharedCheck_4194_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4176_);
                    leanh::lean_inc(v_fst_4175_);
                    leanh::lean_dec(v_a_4171_);
                    v___x_4178_ = leanh::lean_box(0);
                    v_isShared_4179_ = v_isSharedCheck_4194_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_u_4180_ = leanh::lean_ctor_get(v_baseMonadInfo_4144_, 1);
                v_v_4181_ = leanh::lean_ctor_get(v_baseMonadInfo_4144_, 2);
                v___x_4182_ = leanh::lean_box(0);
                leanh::lean_inc(v_v_4181_);
                if v_isShared_4179_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4178_, 1);
                    leanh::lean_ctor_set(v___x_4178_, 1, v___x_4182_);
                    leanh::lean_ctor_set(v___x_4178_, 0, v_v_4181_);
                    v___x_4184_ = v___x_4178_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_v_4181_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 1, v___x_4182_);
                    v___x_4184_ = v_reuseFailAlloc_4193_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_u_4180_);
                if v_isShared_4166_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4165_, 1);
                    leanh::lean_ctor_set(v___x_4165_, 1, v___x_4184_);
                    leanh::lean_ctor_set(v___x_4165_, 0, v_u_4180_);
                    v___x_4186_ = v___x_4165_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_u_4180_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 1, v___x_4184_);
                    v___x_4186_ = v_reuseFailAlloc_4192_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4187_ = l_Lean_mkConst(v_casesOnWrapper_4145_, v___x_4186_);
                v___x_4188_ = l_Lean_mkApp6(
                    v___x_4187_,
                    v_00_u03b5_4146_,
                    v_resultType_4142_,
                    v_snd_4176_,
                    v_a_4156_,
                    v_a_4169_,
                    v_fst_4175_,
                );
                if v_isShared_4174_ == 0 {
                    leanh::lean_ctor_set(v___x_4173_, 0, v___x_4188_);
                    v___x_4190_ = v___x_4173_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4191_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
                    v___x_4190_ = v_reuseFailAlloc_4191_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4190_;
            }
            7 => {
                if v_isShared_4199_ == 0 {
                    v___x_4201_ = v___x_4198_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
                    v___x_4201_ = v_reuseFailAlloc_4202_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4201_;
            }
            9 => {
                if v_isShared_4208_ == 0 {
                    v___x_4210_ = v___x_4207_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
                    v___x_4210_ = v_reuseFailAlloc_4211_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4210_;
            }
            11 => {
                if v_isShared_4216_ == 0 {
                    v___x_4218_ = v___x_4215_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed(
    mut v_a_4221_: *mut leanh::LeanObject,
    mut v_getCont_4222_: *mut leanh::LeanObject,
    mut v_resultName_4223_: *mut leanh::LeanObject,
    mut v_resultType_4224_: *mut leanh::LeanObject,
    mut v___f_4225_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_4226_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_4227_: *mut leanh::LeanObject,
    mut v_00_u03b5_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4237_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__2(
        v_a_4221_,
        v_getCont_4222_,
        v_resultName_4223_,
        v_resultType_4224_,
        v___f_4225_,
        v_baseMonadInfo_4226_,
        v_casesOnWrapper_4227_,
        v_00_u03b5_4228_,
        v___y_4229_,
        v___y_4230_,
        v___y_4231_,
        v___y_4232_,
        v___y_4233_,
        v___y_4234_,
        v___y_4235_,
    );
    leanh::lean_dec(v___y_4235_);
    leanh::lean_dec_ref(v___y_4234_);
    leanh::lean_dec(v___y_4233_);
    leanh::lean_dec_ref(v___y_4232_);
    leanh::lean_dec(v___y_4231_);
    leanh::lean_dec_ref(v___y_4230_);
    leanh::lean_dec_ref(v___y_4229_);
    leanh::lean_dec_ref(v_baseMonadInfo_4226_);
    return v_res_4237_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__3(
    mut v_baseMonadInfo_4238_: *mut leanh::LeanObject,
    mut v_getCont_4239_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_4240_: *mut leanh::LeanObject,
    mut v_00_u03b5_4241_: *mut leanh::LeanObject,
    mut v_restoreCont_4242_: *mut leanh::LeanObject,
    mut v_dec_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
    mut v___y_4246_: *mut leanh::LeanObject,
    mut v___y_4247_: *mut leanh::LeanObject,
    mut v___y_4248_: *mut leanh::LeanObject,
    mut v___y_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultName_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4260_: u8 = 0;
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: u8 = 0;
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4277_: u8 = 0;
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut v_a_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4282_: u8 = 0;
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4252_ = l_Lean_Elab_Do_ControlStack_optionT___lam__5___closed__1;
                v___x_4253_ = l_Lean_Core_mkFreshUserName(v___x_4252_, v___y_4249_, v___y_4250_);
                if leanh::lean_obj_tag(v___x_4253_) == 0 {
                    v_a_4254_ = leanh::lean_ctor_get(v___x_4253_, 0);
                    leanh::lean_inc(v_a_4254_);
                    leanh::lean_dec_ref_known(v___x_4253_, 1);
                    v_resultName_4255_ = leanh::lean_ctor_get(v_dec_4243_, 0);
                    v_resultType_4256_ = leanh::lean_ctor_get(v_dec_4243_, 1);
                    v_k_4257_ = leanh::lean_ctor_get(v_dec_4243_, 2);
                    v_isSharedCheck_4278_ = (!leanh::lean_is_exclusive(v_dec_4243_)) as u8;
                    if v_isSharedCheck_4278_ == 0 {
                        v___x_4259_ = v_dec_4243_;
                        v_isShared_4260_ = v_isSharedCheck_4278_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_4257_);
                        leanh::lean_inc(v_resultType_4256_);
                        leanh::lean_inc(v_resultName_4255_);
                        leanh::lean_dec(v_dec_4243_);
                        v___x_4259_ = leanh::lean_box(0);
                        v_isShared_4260_ = v_isSharedCheck_4278_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_dec_4243_);
                    leanh::lean_dec_ref(v_restoreCont_4242_);
                    leanh::lean_dec_ref(v_00_u03b5_4241_);
                    leanh::lean_dec(v_casesOnWrapper_4240_);
                    leanh::lean_dec_ref(v_getCont_4239_);
                    leanh::lean_dec_ref(v_baseMonadInfo_4238_);
                    v_a_4279_ = leanh::lean_ctor_get(v___x_4253_, 0);
                    v_isSharedCheck_4286_ = (!leanh::lean_is_exclusive(v___x_4253_)) as u8;
                    if v_isSharedCheck_4286_ == 0 {
                        v___x_4281_ = v___x_4253_;
                        v_isShared_4282_ = v_isSharedCheck_4286_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4279_);
                        leanh::lean_dec(v___x_4253_);
                        v___x_4281_ = leanh::lean_box(0);
                        v_isShared_4282_ = v_isSharedCheck_4286_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_resultType_4256_);
                leanh::lean_inc_ref(v_getCont_4239_);
                v___x_4261_ =
                    l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(
                        v_baseMonadInfo_4238_,
                        v_getCont_4239_,
                        v_resultType_4256_,
                        v___y_4244_,
                        v___y_4245_,
                        v___y_4246_,
                        v___y_4247_,
                        v___y_4248_,
                        v___y_4249_,
                        v___y_4250_,
                    );
                if leanh::lean_obj_tag(v___x_4261_) == 0 {
                    v_a_4262_ = leanh::lean_ctor_get(v___x_4261_, 0);
                    leanh::lean_inc(v_a_4262_);
                    leanh::lean_dec_ref_known(v___x_4261_, 1);
                    v___f_4263_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_ControlStack_exceptT___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    leanh::lean_closure_set(v___f_4263_, 0, v_k_4257_);
                    leanh::lean_inc(v_a_4254_);
                    v___f_4264_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_ControlStack_exceptT___lam__2___boxed
                            as *mut core::ffi::c_void,
                        16,
                        8,
                    );
                    leanh::lean_closure_set(v___f_4264_, 0, v_a_4254_);
                    leanh::lean_closure_set(v___f_4264_, 1, v_getCont_4239_);
                    leanh::lean_closure_set(v___f_4264_, 2, v_resultName_4255_);
                    leanh::lean_closure_set(v___f_4264_, 3, v_resultType_4256_);
                    leanh::lean_closure_set(v___f_4264_, 4, v___f_4263_);
                    leanh::lean_closure_set(v___f_4264_, 5, v_baseMonadInfo_4238_);
                    leanh::lean_closure_set(v___f_4264_, 6, v_casesOnWrapper_4240_);
                    leanh::lean_closure_set(v___f_4264_, 7, v_00_u03b5_4241_);
                    v___x_4265_ = 0;
                    if v_isShared_4260_ == 0 {
                        leanh::lean_ctor_set(v___x_4259_, 2, v___f_4264_);
                        leanh::lean_ctor_set(v___x_4259_, 1, v_a_4262_);
                        leanh::lean_ctor_set(v___x_4259_, 0, v_a_4254_);
                        v___x_4267_ = v___x_4259_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4269_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4254_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_a_4262_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 2, v___f_4264_);
                        v___x_4267_ = v_reuseFailAlloc_4269_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4259_);
                    leanh::lean_dec_ref(v_k_4257_);
                    leanh::lean_dec_ref(v_resultType_4256_);
                    leanh::lean_dec(v_resultName_4255_);
                    leanh::lean_dec(v_a_4254_);
                    leanh::lean_dec_ref(v_restoreCont_4242_);
                    leanh::lean_dec_ref(v_00_u03b5_4241_);
                    leanh::lean_dec(v_casesOnWrapper_4240_);
                    leanh::lean_dec_ref(v_getCont_4239_);
                    leanh::lean_dec_ref(v_baseMonadInfo_4238_);
                    v_a_4270_ = leanh::lean_ctor_get(v___x_4261_, 0);
                    v_isSharedCheck_4277_ = (!leanh::lean_is_exclusive(v___x_4261_)) as u8;
                    if v_isSharedCheck_4277_ == 0 {
                        v___x_4272_ = v___x_4261_;
                        v_isShared_4273_ = v_isSharedCheck_4277_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4270_);
                        leanh::lean_dec(v___x_4261_);
                        v___x_4272_ = leanh::lean_box(0);
                        v_isShared_4273_ = v_isSharedCheck_4277_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4267_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4265_,
                );
                leanh::lean_inc(v___y_4250_);
                leanh::lean_inc_ref(v___y_4249_);
                leanh::lean_inc(v___y_4248_);
                leanh::lean_inc_ref(v___y_4247_);
                leanh::lean_inc(v___y_4246_);
                leanh::lean_inc_ref(v___y_4245_);
                leanh::lean_inc_ref(v___y_4244_);
                v___x_4268_ = leanh::lean_apply_9(
                    v_restoreCont_4242_,
                    v___x_4267_,
                    v___y_4244_,
                    v___y_4245_,
                    v___y_4246_,
                    v___y_4247_,
                    v___y_4248_,
                    v___y_4249_,
                    v___y_4250_,
                    leanh::lean_box(0),
                );
                return v___x_4268_;
            }
            3 => {
                if v_isShared_4273_ == 0 {
                    v___x_4275_ = v___x_4272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
                    v___x_4275_ = v_reuseFailAlloc_4276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4275_;
            }
            5 => {
                if v_isShared_4282_ == 0 {
                    v___x_4284_ = v___x_4281_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4285_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
                    v___x_4284_ = v_reuseFailAlloc_4285_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed(
    mut v_baseMonadInfo_4287_: *mut leanh::LeanObject,
    mut v_getCont_4288_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_4289_: *mut leanh::LeanObject,
    mut v_00_u03b5_4290_: *mut leanh::LeanObject,
    mut v_restoreCont_4291_: *mut leanh::LeanObject,
    mut v_dec_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
    mut v___y_4294_: *mut leanh::LeanObject,
    mut v___y_4295_: *mut leanh::LeanObject,
    mut v___y_4296_: *mut leanh::LeanObject,
    mut v___y_4297_: *mut leanh::LeanObject,
    mut v___y_4298_: *mut leanh::LeanObject,
    mut v___y_4299_: *mut leanh::LeanObject,
    mut v___y_4300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4301_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__3(
        v_baseMonadInfo_4287_,
        v_getCont_4288_,
        v_casesOnWrapper_4289_,
        v_00_u03b5_4290_,
        v_restoreCont_4291_,
        v_dec_4292_,
        v___y_4293_,
        v___y_4294_,
        v___y_4295_,
        v___y_4296_,
        v___y_4297_,
        v___y_4298_,
        v___y_4299_,
    );
    leanh::lean_dec(v___y_4299_);
    leanh::lean_dec_ref(v___y_4298_);
    leanh::lean_dec(v___y_4297_);
    leanh::lean_dec_ref(v___y_4296_);
    leanh::lean_dec(v___y_4295_);
    leanh::lean_dec_ref(v___y_4294_);
    leanh::lean_dec_ref(v___y_4293_);
    return v_res_4301_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4303_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__0;
    v___x_4304_ = l_Lean_stringToMessageData(v___x_4303_);
    return v___x_4304_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4306_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__2;
    v___x_4307_ = l_Lean_stringToMessageData(v___x_4306_);
    return v___x_4307_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__4(
    mut v_00_u03b5_4308_: *mut leanh::LeanObject,
    mut v_description_4309_: *mut leanh::LeanObject,
    mut v_x_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4311_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1_once),
        _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__1,
    );
    v___x_4312_ = l_Lean_MessageData_ofExpr(v_00_u03b5_4308_);
    v___x_4313_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4313_, 0, v___x_4311_);
    leanh::lean_ctor_set(v___x_4313_, 1, v___x_4312_);
    v___x_4314_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3_once),
        _init_l_Lean_Elab_Do_ControlStack_exceptT___lam__4___closed__3,
    );
    v___x_4315_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4315_, 0, v___x_4313_);
    leanh::lean_ctor_set(v___x_4315_, 1, v___x_4314_);
    v___x_4316_ = leanh::lean_box(0);
    v___x_4317_ = leanh::lean_apply_1(v_description_4309_, v___x_4316_);
    v___x_4318_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4318_, 0, v___x_4315_);
    leanh::lean_ctor_set(v___x_4318_, 1, v___x_4317_);
    return v___x_4318_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__5(
    mut v_baseMonadInfo_4319_: *mut leanh::LeanObject,
    mut v_getCont_4320_: *mut leanh::LeanObject,
    mut v_stM_4321_: *mut leanh::LeanObject,
    mut v_00_u03b1_4322_: *mut leanh::LeanObject,
    mut v___y_4323_: *mut leanh::LeanObject,
    mut v___y_4324_: *mut leanh::LeanObject,
    mut v___y_4325_: *mut leanh::LeanObject,
    mut v___y_4326_: *mut leanh::LeanObject,
    mut v___y_4327_: *mut leanh::LeanObject,
    mut v___y_4328_: *mut leanh::LeanObject,
    mut v___y_4329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4331_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM(
        v_baseMonadInfo_4319_,
        v_getCont_4320_,
        v_00_u03b1_4322_,
        v___y_4323_,
        v___y_4324_,
        v___y_4325_,
        v___y_4326_,
        v___y_4327_,
        v___y_4328_,
        v___y_4329_,
    );
    if leanh::lean_obj_tag(v___x_4331_) == 0 {
        let mut v_a_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4332_ = leanh::lean_ctor_get(v___x_4331_, 0);
        leanh::lean_inc(v_a_4332_);
        leanh::lean_dec_ref_known(v___x_4331_, 1);
        leanh::lean_inc(v___y_4329_);
        leanh::lean_inc_ref(v___y_4328_);
        leanh::lean_inc(v___y_4327_);
        leanh::lean_inc_ref(v___y_4326_);
        leanh::lean_inc(v___y_4325_);
        leanh::lean_inc_ref(v___y_4324_);
        leanh::lean_inc_ref(v___y_4323_);
        v___x_4333_ = leanh::lean_apply_9(
            v_stM_4321_,
            v_a_4332_,
            v___y_4323_,
            v___y_4324_,
            v___y_4325_,
            v___y_4326_,
            v___y_4327_,
            v___y_4328_,
            v___y_4329_,
            leanh::lean_box(0),
        );
        return v___x_4333_;
    } else {
        leanh::lean_dec_ref(v_stM_4321_);
        return v___x_4331_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed(
    mut v_baseMonadInfo_4334_: *mut leanh::LeanObject,
    mut v_getCont_4335_: *mut leanh::LeanObject,
    mut v_stM_4336_: *mut leanh::LeanObject,
    mut v_00_u03b1_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
    mut v___y_4344_: *mut leanh::LeanObject,
    mut v___y_4345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4346_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__5(
        v_baseMonadInfo_4334_,
        v_getCont_4335_,
        v_stM_4336_,
        v_00_u03b1_4337_,
        v___y_4338_,
        v___y_4339_,
        v___y_4340_,
        v___y_4341_,
        v___y_4342_,
        v___y_4343_,
        v___y_4344_,
    );
    leanh::lean_dec(v___y_4344_);
    leanh::lean_dec_ref(v___y_4343_);
    leanh::lean_dec(v___y_4342_);
    leanh::lean_dec_ref(v___y_4341_);
    leanh::lean_dec(v___y_4340_);
    leanh::lean_dec_ref(v___y_4339_);
    leanh::lean_dec_ref(v___y_4338_);
    leanh::lean_dec_ref(v_baseMonadInfo_4334_);
    return v_res_4346_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__6(
    mut v_runInBase_4351_: *mut leanh::LeanObject,
    mut v_e_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
    mut v___y_4354_: *mut leanh::LeanObject,
    mut v___y_4355_: *mut leanh::LeanObject,
    mut v___y_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4361_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6___closed__1;
    v___x_4362_ = leanh::lean_unsigned_to_nat(1);
    v___x_4363_ = lean_mk_empty_array_with_capacity(v___x_4362_);
    v___x_4364_ = lean_array_push(v___x_4363_, v_e_4352_);
    v___x_4365_ = l_Lean_Meta_mkAppM(
        v___x_4361_,
        v___x_4364_,
        v___y_4356_,
        v___y_4357_,
        v___y_4358_,
        v___y_4359_,
    );
    if leanh::lean_obj_tag(v___x_4365_) == 0 {
        let mut v_a_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4366_ = leanh::lean_ctor_get(v___x_4365_, 0);
        leanh::lean_inc(v_a_4366_);
        leanh::lean_dec_ref_known(v___x_4365_, 1);
        leanh::lean_inc(v___y_4359_);
        leanh::lean_inc_ref(v___y_4358_);
        leanh::lean_inc(v___y_4357_);
        leanh::lean_inc_ref(v___y_4356_);
        leanh::lean_inc(v___y_4355_);
        leanh::lean_inc_ref(v___y_4354_);
        leanh::lean_inc_ref(v___y_4353_);
        v___x_4367_ = leanh::lean_apply_9(
            v_runInBase_4351_,
            v_a_4366_,
            v___y_4353_,
            v___y_4354_,
            v___y_4355_,
            v___y_4356_,
            v___y_4357_,
            v___y_4358_,
            v___y_4359_,
            leanh::lean_box(0),
        );
        return v___x_4367_;
    } else {
        leanh::lean_dec_ref(v_runInBase_4351_);
        return v___x_4365_;
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed(
    mut v_runInBase_4368_: *mut leanh::LeanObject,
    mut v_e_4369_: *mut leanh::LeanObject,
    mut v___y_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
    mut v___y_4372_: *mut leanh::LeanObject,
    mut v___y_4373_: *mut leanh::LeanObject,
    mut v___y_4374_: *mut leanh::LeanObject,
    mut v___y_4375_: *mut leanh::LeanObject,
    mut v___y_4376_: *mut leanh::LeanObject,
    mut v___y_4377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4378_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__6(
        v_runInBase_4368_,
        v_e_4369_,
        v___y_4370_,
        v___y_4371_,
        v___y_4372_,
        v___y_4373_,
        v___y_4374_,
        v___y_4375_,
        v___y_4376_,
    );
    leanh::lean_dec(v___y_4376_);
    leanh::lean_dec_ref(v___y_4375_);
    leanh::lean_dec(v___y_4374_);
    leanh::lean_dec_ref(v___y_4373_);
    leanh::lean_dec(v___y_4372_);
    leanh::lean_dec_ref(v___y_4371_);
    leanh::lean_dec_ref(v___y_4370_);
    return v_res_4378_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__7(
    mut v_m_4379_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_4380_: *mut leanh::LeanObject,
    mut v_exceptTWrapper_4381_: *mut leanh::LeanObject,
    mut v_00_u03b5_4382_: *mut leanh::LeanObject,
    mut v___y_4383_: *mut leanh::LeanObject,
    mut v___y_4384_: *mut leanh::LeanObject,
    mut v___y_4385_: *mut leanh::LeanObject,
    mut v___y_4386_: *mut leanh::LeanObject,
    mut v___y_4387_: *mut leanh::LeanObject,
    mut v___y_4388_: *mut leanh::LeanObject,
    mut v___y_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4395_: u8 = 0;
    let mut v_u_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_4389_);
                leanh::lean_inc_ref(v___y_4388_);
                leanh::lean_inc(v___y_4387_);
                leanh::lean_inc_ref(v___y_4386_);
                leanh::lean_inc(v___y_4385_);
                leanh::lean_inc_ref(v___y_4384_);
                leanh::lean_inc_ref(v___y_4383_);
                v___x_4391_ = leanh::lean_apply_8(
                    v_m_4379_,
                    v___y_4383_,
                    v___y_4384_,
                    v___y_4385_,
                    v___y_4386_,
                    v___y_4387_,
                    v___y_4388_,
                    v___y_4389_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4391_) == 0 {
                    v_a_4392_ = leanh::lean_ctor_get(v___x_4391_, 0);
                    v_isSharedCheck_4406_ = (!leanh::lean_is_exclusive(v___x_4391_)) as u8;
                    if v_isSharedCheck_4406_ == 0 {
                        v___x_4394_ = v___x_4391_;
                        v_isShared_4395_ = v_isSharedCheck_4406_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4392_);
                        leanh::lean_dec(v___x_4391_);
                        v___x_4394_ = leanh::lean_box(0);
                        v_isShared_4395_ = v_isSharedCheck_4406_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_00_u03b5_4382_);
                    leanh::lean_dec(v_exceptTWrapper_4381_);
                    return v___x_4391_;
                }
            }
            1 => {
                v_u_4396_ = leanh::lean_ctor_get(v_baseMonadInfo_4380_, 1);
                v_v_4397_ = leanh::lean_ctor_get(v_baseMonadInfo_4380_, 2);
                v___x_4398_ = leanh::lean_box(0);
                leanh::lean_inc(v_v_4397_);
                v___x_4399_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4399_, 0, v_v_4397_);
                leanh::lean_ctor_set(v___x_4399_, 1, v___x_4398_);
                leanh::lean_inc(v_u_4396_);
                v___x_4400_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4400_, 0, v_u_4396_);
                leanh::lean_ctor_set(v___x_4400_, 1, v___x_4399_);
                v___x_4401_ = l_Lean_mkConst(v_exceptTWrapper_4381_, v___x_4400_);
                v___x_4402_ = l_Lean_mkAppB(v___x_4401_, v_00_u03b5_4382_, v_a_4392_);
                if v_isShared_4395_ == 0 {
                    leanh::lean_ctor_set(v___x_4394_, 0, v___x_4402_);
                    v___x_4404_ = v___x_4394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4402_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed(
    mut v_m_4407_: *mut leanh::LeanObject,
    mut v_baseMonadInfo_4408_: *mut leanh::LeanObject,
    mut v_exceptTWrapper_4409_: *mut leanh::LeanObject,
    mut v_00_u03b5_4410_: *mut leanh::LeanObject,
    mut v___y_4411_: *mut leanh::LeanObject,
    mut v___y_4412_: *mut leanh::LeanObject,
    mut v___y_4413_: *mut leanh::LeanObject,
    mut v___y_4414_: *mut leanh::LeanObject,
    mut v___y_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
    mut v___y_4417_: *mut leanh::LeanObject,
    mut v___y_4418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4419_ = l_Lean_Elab_Do_ControlStack_exceptT___lam__7(
        v_m_4407_,
        v_baseMonadInfo_4408_,
        v_exceptTWrapper_4409_,
        v_00_u03b5_4410_,
        v___y_4411_,
        v___y_4412_,
        v___y_4413_,
        v___y_4414_,
        v___y_4415_,
        v___y_4416_,
        v___y_4417_,
    );
    leanh::lean_dec(v___y_4417_);
    leanh::lean_dec_ref(v___y_4416_);
    leanh::lean_dec(v___y_4415_);
    leanh::lean_dec_ref(v___y_4414_);
    leanh::lean_dec(v___y_4413_);
    leanh::lean_dec_ref(v___y_4412_);
    leanh::lean_dec_ref(v___y_4411_);
    leanh::lean_dec_ref(v_baseMonadInfo_4408_);
    return v_res_4419_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_exceptT(
    mut v_baseMonadInfo_4420_: *mut leanh::LeanObject,
    mut v_exceptTWrapper_4421_: *mut leanh::LeanObject,
    mut v_casesOnWrapper_4422_: *mut leanh::LeanObject,
    mut v_getCont_4423_: *mut leanh::LeanObject,
    mut v_00_u03b5_4424_: *mut leanh::LeanObject,
    mut v_base_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_description_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stM_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_runInBase_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreCont_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___f_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_description_4426_ = leanh::lean_ctor_get(v_base_4425_, 0);
                v_m_4427_ = leanh::lean_ctor_get(v_base_4425_, 1);
                v_stM_4428_ = leanh::lean_ctor_get(v_base_4425_, 2);
                v_runInBase_4429_ = leanh::lean_ctor_get(v_base_4425_, 3);
                v_restoreCont_4430_ = leanh::lean_ctor_get(v_base_4425_, 4);
                v_isSharedCheck_4442_ = (!leanh::lean_is_exclusive(v_base_4425_)) as u8;
                if v_isSharedCheck_4442_ == 0 {
                    v___x_4432_ = v_base_4425_;
                    v_isShared_4433_ = v_isSharedCheck_4442_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_restoreCont_4430_);
                    leanh::lean_inc(v_runInBase_4429_);
                    leanh::lean_inc(v_stM_4428_);
                    leanh::lean_inc(v_m_4427_);
                    leanh::lean_inc(v_description_4426_);
                    leanh::lean_dec(v_base_4425_);
                    v___x_4432_ = leanh::lean_box(0);
                    v_isShared_4433_ = v_isSharedCheck_4442_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v_00_u03b5_4424_, 2);
                leanh::lean_inc_ref(v_getCont_4423_);
                leanh::lean_inc_ref_n(v_baseMonadInfo_4420_, 2);
                v___f_4434_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_exceptT___lam__3___boxed as *mut core::ffi::c_void,
                    14,
                    5,
                );
                leanh::lean_closure_set(v___f_4434_, 0, v_baseMonadInfo_4420_);
                leanh::lean_closure_set(v___f_4434_, 1, v_getCont_4423_);
                leanh::lean_closure_set(v___f_4434_, 2, v_casesOnWrapper_4422_);
                leanh::lean_closure_set(v___f_4434_, 3, v_00_u03b5_4424_);
                leanh::lean_closure_set(v___f_4434_, 4, v_restoreCont_4430_);
                v___f_4435_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_exceptT___lam__4 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_4435_, 0, v_00_u03b5_4424_);
                leanh::lean_closure_set(v___f_4435_, 1, v_description_4426_);
                v___f_4436_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_exceptT___lam__5___boxed as *mut core::ffi::c_void,
                    12,
                    3,
                );
                leanh::lean_closure_set(v___f_4436_, 0, v_baseMonadInfo_4420_);
                leanh::lean_closure_set(v___f_4436_, 1, v_getCont_4423_);
                leanh::lean_closure_set(v___f_4436_, 2, v_stM_4428_);
                v___f_4437_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_exceptT___lam__6___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                leanh::lean_closure_set(v___f_4437_, 0, v_runInBase_4429_);
                v___f_4438_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_exceptT___lam__7___boxed as *mut core::ffi::c_void,
                    12,
                    4,
                );
                leanh::lean_closure_set(v___f_4438_, 0, v_m_4427_);
                leanh::lean_closure_set(v___f_4438_, 1, v_baseMonadInfo_4420_);
                leanh::lean_closure_set(v___f_4438_, 2, v_exceptTWrapper_4421_);
                leanh::lean_closure_set(v___f_4438_, 3, v_00_u03b5_4424_);
                if v_isShared_4433_ == 0 {
                    leanh::lean_ctor_set(v___x_4432_, 4, v___f_4434_);
                    leanh::lean_ctor_set(v___x_4432_, 3, v___f_4437_);
                    leanh::lean_ctor_set(v___x_4432_, 2, v___f_4436_);
                    leanh::lean_ctor_set(v___x_4432_, 1, v___f_4438_);
                    leanh::lean_ctor_set(v___x_4432_, 0, v___f_4435_);
                    v___x_4440_ = v___x_4432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___f_4435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 1, v___f_4438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 2, v___f_4436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 3, v___f_4437_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 4, v___f_4434_);
                    v___x_4440_ = v_reuseFailAlloc_4441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_earlyReturnT(
    mut v_baseMonadInfo_4452_: *mut leanh::LeanObject,
    mut v_00_u03c1_4453_: *mut leanh::LeanObject,
    mut v_m_4454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__1;
    v___x_4456_ = l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__4;
    v___x_4457_ = l_Lean_Elab_Do_ControlStack_earlyReturnT___closed__5;
    v___x_4458_ = l_Lean_Elab_Do_ControlStack_exceptT(
        v_baseMonadInfo_4452_,
        v___x_4455_,
        v___x_4456_,
        v___x_4457_,
        v_00_u03c1_4453_,
        v_m_4454_,
    );
    return v___x_4458_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__0;
    v___x_4461_ = l_Lean_stringToMessageData(v___x_4460_);
    return v___x_4461_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_breakT___lam__0(
    mut v___y_4462_: *mut leanh::LeanObject,
    mut v___y_4463_: *mut leanh::LeanObject,
    mut v___y_4464_: *mut leanh::LeanObject,
    mut v___y_4465_: *mut leanh::LeanObject,
    mut v___y_4466_: *mut leanh::LeanObject,
    mut v___y_4467_: *mut leanh::LeanObject,
    mut v___y_4468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4481_: u8 = 0;
    let mut v_a_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4485_: u8 = 0;
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4470_ = l_Lean_Elab_Do_getBreakCont___redArg(v___y_4462_);
                if leanh::lean_obj_tag(v___x_4470_) == 0 {
                    v_a_4471_ = leanh::lean_ctor_get(v___x_4470_, 0);
                    v_isSharedCheck_4481_ = (!leanh::lean_is_exclusive(v___x_4470_)) as u8;
                    if v_isSharedCheck_4481_ == 0 {
                        v___x_4473_ = v___x_4470_;
                        v_isShared_4474_ = v_isSharedCheck_4481_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4471_);
                        leanh::lean_dec(v___x_4470_);
                        v___x_4473_ = leanh::lean_box(0);
                        v_isShared_4474_ = v_isSharedCheck_4481_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4482_ = leanh::lean_ctor_get(v___x_4470_, 0);
                    v_isSharedCheck_4489_ = (!leanh::lean_is_exclusive(v___x_4470_)) as u8;
                    if v_isSharedCheck_4489_ == 0 {
                        v___x_4484_ = v___x_4470_;
                        v_isShared_4485_ = v_isSharedCheck_4489_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4482_);
                        leanh::lean_dec(v___x_4470_);
                        v___x_4484_ = leanh::lean_box(0);
                        v_isShared_4485_ = v_isSharedCheck_4489_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4471_) == 0 {
                    leanh::lean_del_object(v___x_4473_);
                    v___x_4475_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Do_ControlStack_breakT___lam__0___closed__1,
                    );
                    v___x_4476_ =
                        l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
                            v___x_4475_,
                            v___y_4465_,
                            v___y_4466_,
                            v___y_4467_,
                            v___y_4468_,
                        );
                    return v___x_4476_;
                } else {
                    v_val_4477_ = leanh::lean_ctor_get(v_a_4471_, 0);
                    leanh::lean_inc(v_val_4477_);
                    leanh::lean_dec_ref_known(v_a_4471_, 1);
                    if v_isShared_4474_ == 0 {
                        leanh::lean_ctor_set(v___x_4473_, 0, v_val_4477_);
                        v___x_4479_ = v___x_4473_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4480_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_val_4477_);
                        v___x_4479_ = v_reuseFailAlloc_4480_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4479_;
            }
            3 => {
                if v_isShared_4485_ == 0 {
                    v___x_4487_ = v___x_4484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
                    v___x_4487_ = v_reuseFailAlloc_4488_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_breakT___lam__0___boxed(
    mut v___y_4490_: *mut leanh::LeanObject,
    mut v___y_4491_: *mut leanh::LeanObject,
    mut v___y_4492_: *mut leanh::LeanObject,
    mut v___y_4493_: *mut leanh::LeanObject,
    mut v___y_4494_: *mut leanh::LeanObject,
    mut v___y_4495_: *mut leanh::LeanObject,
    mut v___y_4496_: *mut leanh::LeanObject,
    mut v___y_4497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4498_ = l_Lean_Elab_Do_ControlStack_breakT___lam__0(
        v___y_4490_,
        v___y_4491_,
        v___y_4492_,
        v___y_4493_,
        v___y_4494_,
        v___y_4495_,
        v___y_4496_,
    );
    leanh::lean_dec(v___y_4496_);
    leanh::lean_dec_ref(v___y_4495_);
    leanh::lean_dec(v___y_4494_);
    leanh::lean_dec_ref(v___y_4493_);
    leanh::lean_dec(v___y_4492_);
    leanh::lean_dec_ref(v___y_4491_);
    leanh::lean_dec_ref(v___y_4490_);
    return v_res_4498_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_breakT(
    mut v_baseMonadInfo_4507_: *mut leanh::LeanObject,
    mut v_m_4508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCont_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCont_4509_ = l_Lean_Elab_Do_ControlStack_breakT___closed__0;
    v___x_4510_ = l_Lean_Elab_Do_ControlStack_breakT___closed__2;
    v___x_4511_ = l_Lean_Elab_Do_ControlStack_breakT___closed__4;
    v___x_4512_ = l_Lean_Elab_Do_ControlStack_optionT(
        v_baseMonadInfo_4507_,
        v___x_4510_,
        v___x_4511_,
        v_getCont_4509_,
        v_m_4508_,
    );
    return v___x_4512_;
}
pub unsafe fn _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4514_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__0;
    v___x_4515_ = l_Lean_stringToMessageData(v___x_4514_);
    return v___x_4515_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_continueT___lam__0(
    mut v___y_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
    mut v___y_4519_: *mut leanh::LeanObject,
    mut v___y_4520_: *mut leanh::LeanObject,
    mut v___y_4521_: *mut leanh::LeanObject,
    mut v___y_4522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4528_: u8 = 0;
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut v_a_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4539_: u8 = 0;
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4524_ = l_Lean_Elab_Do_getContinueCont___redArg(v___y_4516_);
                if leanh::lean_obj_tag(v___x_4524_) == 0 {
                    v_a_4525_ = leanh::lean_ctor_get(v___x_4524_, 0);
                    v_isSharedCheck_4535_ = (!leanh::lean_is_exclusive(v___x_4524_)) as u8;
                    if v_isSharedCheck_4535_ == 0 {
                        v___x_4527_ = v___x_4524_;
                        v_isShared_4528_ = v_isSharedCheck_4535_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4525_);
                        leanh::lean_dec(v___x_4524_);
                        v___x_4527_ = leanh::lean_box(0);
                        v_isShared_4528_ = v_isSharedCheck_4535_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4536_ = leanh::lean_ctor_get(v___x_4524_, 0);
                    v_isSharedCheck_4543_ = (!leanh::lean_is_exclusive(v___x_4524_)) as u8;
                    if v_isSharedCheck_4543_ == 0 {
                        v___x_4538_ = v___x_4524_;
                        v_isShared_4539_ = v_isSharedCheck_4543_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4536_);
                        leanh::lean_dec(v___x_4524_);
                        v___x_4538_ = leanh::lean_box(0);
                        v_isShared_4539_ = v_isSharedCheck_4543_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4525_) == 0 {
                    leanh::lean_del_object(v___x_4527_);
                    v___x_4529_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Do_ControlStack_continueT___lam__0___closed__1,
                    );
                    v___x_4530_ =
                        l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
                            v___x_4529_,
                            v___y_4519_,
                            v___y_4520_,
                            v___y_4521_,
                            v___y_4522_,
                        );
                    return v___x_4530_;
                } else {
                    v_val_4531_ = leanh::lean_ctor_get(v_a_4525_, 0);
                    leanh::lean_inc(v_val_4531_);
                    leanh::lean_dec_ref_known(v_a_4525_, 1);
                    if v_isShared_4528_ == 0 {
                        leanh::lean_ctor_set(v___x_4527_, 0, v_val_4531_);
                        v___x_4533_ = v___x_4527_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_val_4531_);
                        v___x_4533_ = v_reuseFailAlloc_4534_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4533_;
            }
            3 => {
                if v_isShared_4539_ == 0 {
                    v___x_4541_ = v___x_4538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
                    v___x_4541_ = v_reuseFailAlloc_4542_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_continueT___lam__0___boxed(
    mut v___y_4544_: *mut leanh::LeanObject,
    mut v___y_4545_: *mut leanh::LeanObject,
    mut v___y_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
    mut v___y_4549_: *mut leanh::LeanObject,
    mut v___y_4550_: *mut leanh::LeanObject,
    mut v___y_4551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_Elab_Do_ControlStack_continueT___lam__0(
        v___y_4544_,
        v___y_4545_,
        v___y_4546_,
        v___y_4547_,
        v___y_4548_,
        v___y_4549_,
        v___y_4550_,
    );
    leanh::lean_dec(v___y_4550_);
    leanh::lean_dec_ref(v___y_4549_);
    leanh::lean_dec(v___y_4548_);
    leanh::lean_dec_ref(v___y_4547_);
    leanh::lean_dec(v___y_4546_);
    leanh::lean_dec_ref(v___y_4545_);
    leanh::lean_dec_ref(v___y_4544_);
    return v_res_4552_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_continueT(
    mut v_baseMonadInfo_4561_: *mut leanh::LeanObject,
    mut v_m_4562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCont_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCont_4563_ = l_Lean_Elab_Do_ControlStack_continueT___closed__0;
    v___x_4564_ = l_Lean_Elab_Do_ControlStack_continueT___closed__2;
    v___x_4565_ = l_Lean_Elab_Do_ControlStack_continueT___closed__4;
    v___x_4566_ = l_Lean_Elab_Do_ControlStack_optionT(
        v_baseMonadInfo_4561_,
        v___x_4564_,
        v___x_4565_,
        v_getCont_4563_,
        v_m_4562_,
    );
    return v___x_4566_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(
    mut v_mi_4570_: *mut leanh::LeanObject,
    mut v_a_4571_: *mut leanh::LeanObject,
    mut v_a_4572_: *mut leanh::LeanObject,
    mut v_a_4573_: *mut leanh::LeanObject,
    mut v_a_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
    mut v_a_4576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_m_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_m_4578_ = leanh::lean_ctor_get(v_mi_4570_, 0);
    leanh::lean_inc_ref(v_m_4578_);
    v_u_4579_ = leanh::lean_ctor_get(v_mi_4570_, 1);
    leanh::lean_inc(v_u_4579_);
    v_v_4580_ = leanh::lean_ctor_get(v_mi_4570_, 2);
    leanh::lean_inc(v_v_4580_);
    leanh::lean_dec_ref(v_mi_4570_);
    v___x_4581_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___closed__1;
    v___x_4582_ = leanh::lean_box(0);
    v___x_4583_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4583_, 0, v_v_4580_);
    leanh::lean_ctor_set(v___x_4583_, 1, v___x_4582_);
    v___x_4584_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4584_, 0, v_u_4579_);
    leanh::lean_ctor_set(v___x_4584_, 1, v___x_4583_);
    v___x_4585_ = l_Lean_mkConst(v___x_4581_, v___x_4584_);
    v___x_4586_ = l_Lean_Expr_app___override(v___x_4585_, v_m_4578_);
    v___x_4587_ = leanh::lean_box(0);
    v___x_4588_ = l_Lean_Elab_Term_mkInstMVar(
        v___x_4586_,
        v___x_4587_,
        v_a_4571_,
        v_a_4572_,
        v_a_4573_,
        v_a_4574_,
        v_a_4575_,
        v_a_4576_,
    );
    return v___x_4588_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad___boxed(
    mut v_mi_4589_: *mut leanh::LeanObject,
    mut v_a_4590_: *mut leanh::LeanObject,
    mut v_a_4591_: *mut leanh::LeanObject,
    mut v_a_4592_: *mut leanh::LeanObject,
    mut v_a_4593_: *mut leanh::LeanObject,
    mut v_a_4594_: *mut leanh::LeanObject,
    mut v_a_4595_: *mut leanh::LeanObject,
    mut v_a_4596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4597_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(
        v_mi_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_,
    );
    leanh::lean_dec(v_a_4595_);
    leanh::lean_dec_ref(v_a_4594_);
    leanh::lean_dec(v_a_4593_);
    leanh::lean_dec_ref(v_a_4592_);
    leanh::lean_dec(v_a_4591_);
    leanh::lean_dec_ref(v_a_4590_);
    return v_res_4597_;
}
pub unsafe fn _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4599_ =
        l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__0;
    v___x_4600_ = l_Lean_stringToMessageData(v___x_4599_);
    return v___x_4600_;
}
pub unsafe fn _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4602_ =
        l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__2;
    v___x_4603_ = l_Lean_stringToMessageData(v___x_4602_);
    return v___x_4603_;
}
pub unsafe fn _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4605_ =
        l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__4;
    v___x_4606_ = l_Lean_stringToMessageData(v___x_4605_);
    return v___x_4606_;
}
pub unsafe fn _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4608_ =
        l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__6;
    v___x_4609_ = l_Lean_stringToMessageData(v___x_4608_);
    return v___x_4609_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(
    mut v_msg_4610_: *mut leanh::LeanObject,
    mut v_expected_4611_: *mut leanh::LeanObject,
    mut v_actual_4612_: *mut leanh::LeanObject,
    mut v_a_4613_: *mut leanh::LeanObject,
    mut v_a_4614_: *mut leanh::LeanObject,
    mut v_a_4615_: *mut leanh::LeanObject,
    mut v_a_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4623_: u8 = 0;
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4642_: u8 = 0;
    let mut v_a_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4646_: u8 = 0;
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_actual_4612_);
                leanh::lean_inc_ref(v_expected_4611_);
                v___x_4618_ = l_Lean_Meta_isExprDefEq(
                    v_expected_4611_,
                    v_actual_4612_,
                    v_a_4613_,
                    v_a_4614_,
                    v_a_4615_,
                    v_a_4616_,
                );
                if leanh::lean_obj_tag(v___x_4618_) == 0 {
                    v_a_4619_ = leanh::lean_ctor_get(v___x_4618_, 0);
                    v_isSharedCheck_4642_ = (!leanh::lean_is_exclusive(v___x_4618_)) as u8;
                    if v_isSharedCheck_4642_ == 0 {
                        v___x_4621_ = v___x_4618_;
                        v_isShared_4622_ = v_isSharedCheck_4642_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4619_);
                        leanh::lean_dec(v___x_4618_);
                        v___x_4621_ = leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4642_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_actual_4612_);
                    leanh::lean_dec_ref(v_expected_4611_);
                    leanh::lean_dec_ref(v_msg_4610_);
                    v_a_4643_ = leanh::lean_ctor_get(v___x_4618_, 0);
                    v_isSharedCheck_4650_ = (!leanh::lean_is_exclusive(v___x_4618_)) as u8;
                    if v_isSharedCheck_4650_ == 0 {
                        v___x_4645_ = v___x_4618_;
                        v_isShared_4646_ = v_isSharedCheck_4650_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4643_);
                        leanh::lean_dec(v___x_4618_);
                        v___x_4645_ = leanh::lean_box(0);
                        v_isShared_4646_ = v_isSharedCheck_4650_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4623_ = (leanh::lean_unbox(v_a_4619_) as u8);
                leanh::lean_dec(v_a_4619_);
                if v___x_4623_ == 0 {
                    leanh::lean_del_object(v___x_4621_);
                    v___x_4624_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1_once), _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__1);
                    v___x_4625_ = l_Lean_stringToMessageData(v_msg_4610_);
                    v___x_4626_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4626_, 0, v___x_4624_);
                    leanh::lean_ctor_set(v___x_4626_, 1, v___x_4625_);
                    v___x_4627_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3_once), _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__3);
                    v___x_4628_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4628_, 0, v___x_4626_);
                    leanh::lean_ctor_set(v___x_4628_, 1, v___x_4627_);
                    v___x_4629_ = l_Lean_MessageData_ofExpr(v_expected_4611_);
                    v___x_4630_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4630_, 0, v___x_4628_);
                    leanh::lean_ctor_set(v___x_4630_, 1, v___x_4629_);
                    v___x_4631_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5_once), _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__5);
                    v___x_4632_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4632_, 0, v___x_4630_);
                    leanh::lean_ctor_set(v___x_4632_, 1, v___x_4631_);
                    v___x_4633_ = l_Lean_MessageData_ofExpr(v_actual_4612_);
                    v___x_4634_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4634_, 0, v___x_4632_);
                    leanh::lean_ctor_set(v___x_4634_, 1, v___x_4633_);
                    v___x_4635_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7_once), _init_l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___closed__7);
                    v___x_4636_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4636_, 0, v___x_4634_);
                    leanh::lean_ctor_set(v___x_4636_, 1, v___x_4635_);
                    v___x_4637_ =
                        l_Lean_throwError___at___00Lean_Elab_Do_ControlStack_unStM_spec__0___redArg(
                            v___x_4636_,
                            v_a_4613_,
                            v_a_4614_,
                            v_a_4615_,
                            v_a_4616_,
                        );
                    return v___x_4637_;
                } else {
                    leanh::lean_dec_ref(v_actual_4612_);
                    leanh::lean_dec_ref(v_expected_4611_);
                    leanh::lean_dec_ref(v_msg_4610_);
                    v___x_4638_ = leanh::lean_box(0);
                    if v_isShared_4622_ == 0 {
                        leanh::lean_ctor_set(v___x_4621_, 0, v___x_4638_);
                        v___x_4640_ = v___x_4621_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4641_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
                        v___x_4640_ = v_reuseFailAlloc_4641_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4640_;
            }
            3 => {
                if v_isShared_4646_ == 0 {
                    v___x_4648_ = v___x_4645_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4649_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
                    v___x_4648_ = v_reuseFailAlloc_4649_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg___boxed(
    mut v_msg_4651_: *mut leanh::LeanObject,
    mut v_expected_4652_: *mut leanh::LeanObject,
    mut v_actual_4653_: *mut leanh::LeanObject,
    mut v_a_4654_: *mut leanh::LeanObject,
    mut v_a_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4659_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(
        v_msg_4651_,
        v_expected_4652_,
        v_actual_4653_,
        v_a_4654_,
        v_a_4655_,
        v_a_4656_,
        v_a_4657_,
    );
    leanh::lean_dec(v_a_4657_);
    leanh::lean_dec_ref(v_a_4656_);
    leanh::lean_dec(v_a_4655_);
    leanh::lean_dec_ref(v_a_4654_);
    return v_res_4659_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(
    mut v_msg_4660_: *mut leanh::LeanObject,
    mut v_expected_4661_: *mut leanh::LeanObject,
    mut v_actual_4662_: *mut leanh::LeanObject,
    mut v_a_4663_: *mut leanh::LeanObject,
    mut v_a_4664_: *mut leanh::LeanObject,
    mut v_a_4665_: *mut leanh::LeanObject,
    mut v_a_4666_: *mut leanh::LeanObject,
    mut v_a_4667_: *mut leanh::LeanObject,
    mut v_a_4668_: *mut leanh::LeanObject,
    mut v_a_4669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4671_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(
        v_msg_4660_,
        v_expected_4661_,
        v_actual_4662_,
        v_a_4666_,
        v_a_4667_,
        v_a_4668_,
        v_a_4669_,
    );
    return v___x_4671_;
}
pub unsafe fn l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___boxed(
    mut v_msg_4672_: *mut leanh::LeanObject,
    mut v_expected_4673_: *mut leanh::LeanObject,
    mut v_actual_4674_: *mut leanh::LeanObject,
    mut v_a_4675_: *mut leanh::LeanObject,
    mut v_a_4676_: *mut leanh::LeanObject,
    mut v_a_4677_: *mut leanh::LeanObject,
    mut v_a_4678_: *mut leanh::LeanObject,
    mut v_a_4679_: *mut leanh::LeanObject,
    mut v_a_4680_: *mut leanh::LeanObject,
    mut v_a_4681_: *mut leanh::LeanObject,
    mut v_a_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4683_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq(
        v_msg_4672_,
        v_expected_4673_,
        v_actual_4674_,
        v_a_4675_,
        v_a_4676_,
        v_a_4677_,
        v_a_4678_,
        v_a_4679_,
        v_a_4680_,
        v_a_4681_,
    );
    leanh::lean_dec(v_a_4681_);
    leanh::lean_dec_ref(v_a_4680_);
    leanh::lean_dec(v_a_4679_);
    leanh::lean_dec_ref(v_a_4678_);
    leanh::lean_dec(v_a_4677_);
    leanh::lean_dec_ref(v_a_4676_);
    leanh::lean_dec_ref(v_a_4675_);
    return v_res_4683_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkBreak(
    mut v_base_4689_: *mut leanh::LeanObject,
    mut v_hasContinue_4690_: u8,
    mut v_a_4691_: *mut leanh::LeanObject,
    mut v_a_4692_: *mut leanh::LeanObject,
    mut v_a_4693_: *mut leanh::LeanObject,
    mut v_a_4694_: *mut leanh::LeanObject,
    mut v_a_4695_: *mut leanh::LeanObject,
    mut v_a_4696_: *mut leanh::LeanObject,
    mut v_a_4697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_m_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_runInBase_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4703_: u8 = 0;
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnit_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnitUnit_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4742_: u8 = 0;
    let mut v_unused_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4758_: u8 = 0;
    let mut v_unused_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_m_4699_ = leanh::lean_ctor_get(v_base_4689_, 1);
                v_runInBase_4700_ = leanh::lean_ctor_get(v_base_4689_, 3);
                v_isSharedCheck_4758_ = (!leanh::lean_is_exclusive(v_base_4689_)) as u8;
                if v_isSharedCheck_4758_ == 0 {
                    v_unused_4759_ = leanh::lean_ctor_get(v_base_4689_, 4);
                    leanh::lean_dec(v_unused_4759_);
                    v_unused_4760_ = leanh::lean_ctor_get(v_base_4689_, 2);
                    leanh::lean_dec(v_unused_4760_);
                    v_unused_4761_ = leanh::lean_ctor_get(v_base_4689_, 0);
                    leanh::lean_dec(v_unused_4761_);
                    v___x_4702_ = v_base_4689_;
                    v_isShared_4703_ = v_isSharedCheck_4758_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_runInBase_4700_);
                    leanh::lean_inc(v_m_4699_);
                    leanh::lean_dec(v_base_4689_);
                    v___x_4702_ = leanh::lean_box(0);
                    v_isShared_4703_ = v_isSharedCheck_4758_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_4697_);
                leanh::lean_inc_ref(v_a_4696_);
                leanh::lean_inc(v_a_4695_);
                leanh::lean_inc_ref(v_a_4694_);
                leanh::lean_inc(v_a_4693_);
                leanh::lean_inc_ref(v_a_4692_);
                leanh::lean_inc_ref(v_a_4691_);
                v___x_4704_ = leanh::lean_apply_8(
                    v_m_4699_,
                    v_a_4691_,
                    v_a_4692_,
                    v_a_4693_,
                    v_a_4694_,
                    v_a_4695_,
                    v_a_4696_,
                    v_a_4697_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4704_) == 0 {
                    v_monadInfo_4705_ = leanh::lean_ctor_get(v_a_4691_, 0);
                    v_a_4706_ = leanh::lean_ctor_get(v___x_4704_, 0);
                    leanh::lean_inc_n(v_a_4706_, 2);
                    leanh::lean_dec_ref_known(v___x_4704_, 1);
                    v_doBlockResultType_4707_ = leanh::lean_ctor_get(v_a_4691_, 3);
                    v_u_4708_ = leanh::lean_ctor_get(v_monadInfo_4705_, 1);
                    v_v_4709_ = leanh::lean_ctor_get(v_monadInfo_4705_, 2);
                    v_cachedPUnit_4710_ = leanh::lean_ctor_get(v_monadInfo_4705_, 3);
                    v_cachedPUnitUnit_4711_ = leanh::lean_ctor_get(v_monadInfo_4705_, 4);
                    leanh::lean_inc_ref(v_cachedPUnitUnit_4711_);
                    leanh::lean_inc_ref(v_cachedPUnit_4710_);
                    leanh::lean_inc(v_v_4709_);
                    leanh::lean_inc(v_u_4708_);
                    if v_isShared_4703_ == 0 {
                        leanh::lean_ctor_set(v___x_4702_, 4, v_cachedPUnitUnit_4711_);
                        leanh::lean_ctor_set(v___x_4702_, 3, v_cachedPUnit_4710_);
                        leanh::lean_ctor_set(v___x_4702_, 2, v_v_4709_);
                        leanh::lean_ctor_set(v___x_4702_, 1, v_u_4708_);
                        leanh::lean_ctor_set(v___x_4702_, 0, v_a_4706_);
                        v___x_4713_ = v___x_4702_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4757_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4706_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_u_4708_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_v_4709_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 3, v_cachedPUnit_4710_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_4757_,
                            4,
                            v_cachedPUnitUnit_4711_,
                        );
                        v___x_4713_ = v_reuseFailAlloc_4757_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4702_);
                    leanh::lean_dec_ref(v_runInBase_4700_);
                    return v___x_4704_;
                }
            }
            2 => {
                v___x_4714_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(
                    v___x_4713_,
                    v_a_4692_,
                    v_a_4693_,
                    v_a_4694_,
                    v_a_4695_,
                    v_a_4696_,
                    v_a_4697_,
                );
                if leanh::lean_obj_tag(v___x_4714_) == 0 {
                    v_a_4715_ = leanh::lean_ctor_get(v___x_4714_, 0);
                    leanh::lean_inc(v_a_4715_);
                    leanh::lean_dec_ref_known(v___x_4714_, 1);
                    v___x_4716_ = l_Lean_Elab_Do_ControlStack_unStM___closed__1;
                    v___x_4717_ = 0;
                    v___x_4718_ = l_Lean_Elab_Do_mkFreshResultType___redArg(
                        v___x_4716_,
                        v___x_4717_,
                        v_a_4691_,
                        v_a_4694_,
                        v_a_4695_,
                        v_a_4696_,
                        v_a_4697_,
                    );
                    if leanh::lean_obj_tag(v___x_4718_) == 0 {
                        v_a_4719_ = leanh::lean_ctor_get(v___x_4718_, 0);
                        leanh::lean_inc(v_a_4719_);
                        leanh::lean_dec_ref_known(v___x_4718_, 1);
                        if v_hasContinue_4690_ == 0 {
                            v___y_4721_ = v_a_4719_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4752_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_optionT_stM___closed__1;
                            v___x_4753_ = leanh::lean_box(0);
                            leanh::lean_inc(v_u_4708_);
                            v___x_4754_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4754_, 0, v_u_4708_);
                            leanh::lean_ctor_set(v___x_4754_, 1, v___x_4753_);
                            v___x_4755_ = l_Lean_mkConst(v___x_4752_, v___x_4754_);
                            v___x_4756_ = l_Lean_Expr_app___override(v___x_4755_, v_a_4719_);
                            v___y_4721_ = v___x_4756_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4715_);
                        leanh::lean_dec(v_a_4706_);
                        leanh::lean_dec_ref(v_runInBase_4700_);
                        return v___x_4718_;
                    }
                } else {
                    leanh::lean_dec(v_a_4706_);
                    leanh::lean_dec_ref(v_runInBase_4700_);
                    return v___x_4714_;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_doBlockResultType_4707_);
                v___x_4722_ = l_Lean_Elab_Do_mkMonadApp(
                    v_doBlockResultType_4707_,
                    v_a_4691_,
                    v_a_4692_,
                    v_a_4693_,
                    v_a_4694_,
                    v_a_4695_,
                    v_a_4696_,
                    v_a_4697_,
                );
                if leanh::lean_obj_tag(v___x_4722_) == 0 {
                    v_a_4723_ = leanh::lean_ctor_get(v___x_4722_, 0);
                    leanh::lean_inc(v_a_4723_);
                    leanh::lean_dec_ref_known(v___x_4722_, 1);
                    v___x_4724_ = l_Lean_Elab_Do_ControlStack_mkBreak___closed__1;
                    v___x_4725_ = leanh::lean_box(0);
                    leanh::lean_inc(v_v_4709_);
                    v___x_4726_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4726_, 0, v_v_4709_);
                    leanh::lean_ctor_set(v___x_4726_, 1, v___x_4725_);
                    leanh::lean_inc(v_u_4708_);
                    v___x_4727_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4727_, 0, v_u_4708_);
                    leanh::lean_ctor_set(v___x_4727_, 1, v___x_4726_);
                    v___x_4728_ = l_Lean_mkConst(v___x_4724_, v___x_4727_);
                    v___x_4729_ = l_Lean_mkApp3(v___x_4728_, v___y_4721_, v_a_4706_, v_a_4715_);
                    leanh::lean_inc(v_a_4697_);
                    leanh::lean_inc_ref(v_a_4696_);
                    leanh::lean_inc(v_a_4695_);
                    leanh::lean_inc_ref(v_a_4694_);
                    leanh::lean_inc(v_a_4693_);
                    leanh::lean_inc_ref(v_a_4692_);
                    leanh::lean_inc_ref(v_a_4691_);
                    v___x_4730_ = leanh::lean_apply_9(
                        v_runInBase_4700_,
                        v___x_4729_,
                        v_a_4691_,
                        v_a_4692_,
                        v_a_4693_,
                        v_a_4694_,
                        v_a_4695_,
                        v_a_4696_,
                        v_a_4697_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4730_) == 0 {
                        v_a_4731_ = leanh::lean_ctor_get(v___x_4730_, 0);
                        leanh::lean_inc_n(v_a_4731_, 2);
                        leanh::lean_dec_ref_known(v___x_4730_, 1);
                        leanh::lean_inc(v_a_4697_);
                        leanh::lean_inc_ref(v_a_4696_);
                        leanh::lean_inc(v_a_4695_);
                        leanh::lean_inc_ref(v_a_4694_);
                        v___x_4732_ =
                            lean_infer_type(v_a_4731_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
                        if leanh::lean_obj_tag(v___x_4732_) == 0 {
                            v_a_4733_ = leanh::lean_ctor_get(v___x_4732_, 0);
                            leanh::lean_inc(v_a_4733_);
                            leanh::lean_dec_ref_known(v___x_4732_, 1);
                            v___x_4734_ = l_Lean_Elab_Do_ControlStack_mkBreak___closed__2;
                            v___x_4735_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_4734_, v_a_4723_, v_a_4733_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
                            if leanh::lean_obj_tag(v___x_4735_) == 0 {
                                v_isSharedCheck_4742_ =
                                    (!leanh::lean_is_exclusive(v___x_4735_)) as u8;
                                if v_isSharedCheck_4742_ == 0 {
                                    v_unused_4743_ = leanh::lean_ctor_get(v___x_4735_, 0);
                                    leanh::lean_dec(v_unused_4743_);
                                    v___x_4737_ = v___x_4735_;
                                    v_isShared_4738_ = v_isSharedCheck_4742_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_4735_);
                                    v___x_4737_ = leanh::lean_box(0);
                                    v_isShared_4738_ = v_isSharedCheck_4742_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_4731_);
                                v_a_4744_ = leanh::lean_ctor_get(v___x_4735_, 0);
                                v_isSharedCheck_4751_ =
                                    (!leanh::lean_is_exclusive(v___x_4735_)) as u8;
                                if v_isSharedCheck_4751_ == 0 {
                                    v___x_4746_ = v___x_4735_;
                                    v_isShared_4747_ = v_isSharedCheck_4751_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4744_);
                                    leanh::lean_dec(v___x_4735_);
                                    v___x_4746_ = leanh::lean_box(0);
                                    v_isShared_4747_ = v_isSharedCheck_4751_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4731_);
                            leanh::lean_dec(v_a_4723_);
                            return v___x_4732_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4723_);
                        return v___x_4730_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4721_);
                    leanh::lean_dec(v_a_4715_);
                    leanh::lean_dec(v_a_4706_);
                    leanh::lean_dec_ref(v_runInBase_4700_);
                    return v___x_4722_;
                }
            }
            4 => {
                if v_isShared_4738_ == 0 {
                    leanh::lean_ctor_set(v___x_4737_, 0, v_a_4731_);
                    v___x_4740_ = v___x_4737_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4731_);
                    v___x_4740_ = v_reuseFailAlloc_4741_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4740_;
            }
            6 => {
                if v_isShared_4747_ == 0 {
                    v___x_4749_ = v___x_4746_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4750_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
                    v___x_4749_ = v_reuseFailAlloc_4750_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkBreak___boxed(
    mut v_base_4762_: *mut leanh::LeanObject,
    mut v_hasContinue_4763_: *mut leanh::LeanObject,
    mut v_a_4764_: *mut leanh::LeanObject,
    mut v_a_4765_: *mut leanh::LeanObject,
    mut v_a_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
    mut v_a_4768_: *mut leanh::LeanObject,
    mut v_a_4769_: *mut leanh::LeanObject,
    mut v_a_4770_: *mut leanh::LeanObject,
    mut v_a_4771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hasContinue_boxed_4772_: u8 = 0;
    let mut v_res_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hasContinue_boxed_4772_ = (leanh::lean_unbox(v_hasContinue_4763_) as u8);
    v_res_4773_ = l_Lean_Elab_Do_ControlStack_mkBreak(
        v_base_4762_,
        v_hasContinue_boxed_4772_,
        v_a_4764_,
        v_a_4765_,
        v_a_4766_,
        v_a_4767_,
        v_a_4768_,
        v_a_4769_,
        v_a_4770_,
    );
    leanh::lean_dec(v_a_4770_);
    leanh::lean_dec_ref(v_a_4769_);
    leanh::lean_dec(v_a_4768_);
    leanh::lean_dec_ref(v_a_4767_);
    leanh::lean_dec(v_a_4766_);
    leanh::lean_dec_ref(v_a_4765_);
    leanh::lean_dec_ref(v_a_4764_);
    return v_res_4773_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkContinue(
    mut v_base_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
    mut v_a_4781_: *mut leanh::LeanObject,
    mut v_a_4782_: *mut leanh::LeanObject,
    mut v_a_4783_: *mut leanh::LeanObject,
    mut v_a_4784_: *mut leanh::LeanObject,
    mut v_a_4785_: *mut leanh::LeanObject,
    mut v_a_4786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_m_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_runInBase_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4792_: u8 = 0;
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnit_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnitUnit_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: u8 = 0;
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4829_: u8 = 0;
    let mut v_unused_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4834_: u8 = 0;
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_reuseFailAlloc_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4840_: u8 = 0;
    let mut v_unused_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_m_4788_ = leanh::lean_ctor_get(v_base_4779_, 1);
                v_runInBase_4789_ = leanh::lean_ctor_get(v_base_4779_, 3);
                v_isSharedCheck_4840_ = (!leanh::lean_is_exclusive(v_base_4779_)) as u8;
                if v_isSharedCheck_4840_ == 0 {
                    v_unused_4841_ = leanh::lean_ctor_get(v_base_4779_, 4);
                    leanh::lean_dec(v_unused_4841_);
                    v_unused_4842_ = leanh::lean_ctor_get(v_base_4779_, 2);
                    leanh::lean_dec(v_unused_4842_);
                    v_unused_4843_ = leanh::lean_ctor_get(v_base_4779_, 0);
                    leanh::lean_dec(v_unused_4843_);
                    v___x_4791_ = v_base_4779_;
                    v_isShared_4792_ = v_isSharedCheck_4840_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_runInBase_4789_);
                    leanh::lean_inc(v_m_4788_);
                    leanh::lean_dec(v_base_4779_);
                    v___x_4791_ = leanh::lean_box(0);
                    v_isShared_4792_ = v_isSharedCheck_4840_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_4786_);
                leanh::lean_inc_ref(v_a_4785_);
                leanh::lean_inc(v_a_4784_);
                leanh::lean_inc_ref(v_a_4783_);
                leanh::lean_inc(v_a_4782_);
                leanh::lean_inc_ref(v_a_4781_);
                leanh::lean_inc_ref(v_a_4780_);
                v___x_4793_ = leanh::lean_apply_8(
                    v_m_4788_,
                    v_a_4780_,
                    v_a_4781_,
                    v_a_4782_,
                    v_a_4783_,
                    v_a_4784_,
                    v_a_4785_,
                    v_a_4786_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4793_) == 0 {
                    v_monadInfo_4794_ = leanh::lean_ctor_get(v_a_4780_, 0);
                    v_a_4795_ = leanh::lean_ctor_get(v___x_4793_, 0);
                    leanh::lean_inc_n(v_a_4795_, 2);
                    leanh::lean_dec_ref_known(v___x_4793_, 1);
                    v_doBlockResultType_4796_ = leanh::lean_ctor_get(v_a_4780_, 3);
                    v_u_4797_ = leanh::lean_ctor_get(v_monadInfo_4794_, 1);
                    v_v_4798_ = leanh::lean_ctor_get(v_monadInfo_4794_, 2);
                    v_cachedPUnit_4799_ = leanh::lean_ctor_get(v_monadInfo_4794_, 3);
                    v_cachedPUnitUnit_4800_ = leanh::lean_ctor_get(v_monadInfo_4794_, 4);
                    leanh::lean_inc_ref(v_cachedPUnitUnit_4800_);
                    leanh::lean_inc_ref(v_cachedPUnit_4799_);
                    leanh::lean_inc(v_v_4798_);
                    leanh::lean_inc(v_u_4797_);
                    if v_isShared_4792_ == 0 {
                        leanh::lean_ctor_set(v___x_4791_, 4, v_cachedPUnitUnit_4800_);
                        leanh::lean_ctor_set(v___x_4791_, 3, v_cachedPUnit_4799_);
                        leanh::lean_ctor_set(v___x_4791_, 2, v_v_4798_);
                        leanh::lean_ctor_set(v___x_4791_, 1, v_u_4797_);
                        leanh::lean_ctor_set(v___x_4791_, 0, v_a_4795_);
                        v___x_4802_ = v___x_4791_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4839_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4795_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4839_, 1, v_u_4797_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4839_, 2, v_v_4798_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4839_, 3, v_cachedPUnit_4799_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_4839_,
                            4,
                            v_cachedPUnitUnit_4800_,
                        );
                        v___x_4802_ = v_reuseFailAlloc_4839_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4791_);
                    leanh::lean_dec_ref(v_runInBase_4789_);
                    return v___x_4793_;
                }
            }
            2 => {
                v___x_4803_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(
                    v___x_4802_,
                    v_a_4781_,
                    v_a_4782_,
                    v_a_4783_,
                    v_a_4784_,
                    v_a_4785_,
                    v_a_4786_,
                );
                if leanh::lean_obj_tag(v___x_4803_) == 0 {
                    v_a_4804_ = leanh::lean_ctor_get(v___x_4803_, 0);
                    leanh::lean_inc(v_a_4804_);
                    leanh::lean_dec_ref_known(v___x_4803_, 1);
                    v___x_4805_ = l_Lean_Elab_Do_ControlStack_unStM___closed__1;
                    v___x_4806_ = 0;
                    v___x_4807_ = l_Lean_Elab_Do_mkFreshResultType___redArg(
                        v___x_4805_,
                        v___x_4806_,
                        v_a_4780_,
                        v_a_4783_,
                        v_a_4784_,
                        v_a_4785_,
                        v_a_4786_,
                    );
                    if leanh::lean_obj_tag(v___x_4807_) == 0 {
                        v_a_4808_ = leanh::lean_ctor_get(v___x_4807_, 0);
                        leanh::lean_inc(v_a_4808_);
                        leanh::lean_dec_ref_known(v___x_4807_, 1);
                        leanh::lean_inc_ref(v_doBlockResultType_4796_);
                        v___x_4809_ = l_Lean_Elab_Do_mkMonadApp(
                            v_doBlockResultType_4796_,
                            v_a_4780_,
                            v_a_4781_,
                            v_a_4782_,
                            v_a_4783_,
                            v_a_4784_,
                            v_a_4785_,
                            v_a_4786_,
                        );
                        if leanh::lean_obj_tag(v___x_4809_) == 0 {
                            v_a_4810_ = leanh::lean_ctor_get(v___x_4809_, 0);
                            leanh::lean_inc(v_a_4810_);
                            leanh::lean_dec_ref_known(v___x_4809_, 1);
                            v___x_4811_ = l_Lean_Elab_Do_ControlStack_mkContinue___closed__1;
                            v___x_4812_ = leanh::lean_box(0);
                            leanh::lean_inc(v_v_4798_);
                            v___x_4813_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4813_, 0, v_v_4798_);
                            leanh::lean_ctor_set(v___x_4813_, 1, v___x_4812_);
                            leanh::lean_inc(v_u_4797_);
                            v___x_4814_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4814_, 0, v_u_4797_);
                            leanh::lean_ctor_set(v___x_4814_, 1, v___x_4813_);
                            v___x_4815_ = l_Lean_mkConst(v___x_4811_, v___x_4814_);
                            v___x_4816_ =
                                l_Lean_mkApp3(v___x_4815_, v_a_4808_, v_a_4795_, v_a_4804_);
                            leanh::lean_inc(v_a_4786_);
                            leanh::lean_inc_ref(v_a_4785_);
                            leanh::lean_inc(v_a_4784_);
                            leanh::lean_inc_ref(v_a_4783_);
                            leanh::lean_inc(v_a_4782_);
                            leanh::lean_inc_ref(v_a_4781_);
                            leanh::lean_inc_ref(v_a_4780_);
                            v___x_4817_ = leanh::lean_apply_9(
                                v_runInBase_4789_,
                                v___x_4816_,
                                v_a_4780_,
                                v_a_4781_,
                                v_a_4782_,
                                v_a_4783_,
                                v_a_4784_,
                                v_a_4785_,
                                v_a_4786_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_4817_) == 0 {
                                v_a_4818_ = leanh::lean_ctor_get(v___x_4817_, 0);
                                leanh::lean_inc_n(v_a_4818_, 2);
                                leanh::lean_dec_ref_known(v___x_4817_, 1);
                                leanh::lean_inc(v_a_4786_);
                                leanh::lean_inc_ref(v_a_4785_);
                                leanh::lean_inc(v_a_4784_);
                                leanh::lean_inc_ref(v_a_4783_);
                                v___x_4819_ = lean_infer_type(
                                    v_a_4818_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_,
                                );
                                if leanh::lean_obj_tag(v___x_4819_) == 0 {
                                    v_a_4820_ = leanh::lean_ctor_get(v___x_4819_, 0);
                                    leanh::lean_inc(v_a_4820_);
                                    leanh::lean_dec_ref_known(v___x_4819_, 1);
                                    v___x_4821_ =
                                        l_Lean_Elab_Do_ControlStack_mkContinue___closed__2;
                                    v___x_4822_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_4821_, v_a_4810_, v_a_4820_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
                                    if leanh::lean_obj_tag(v___x_4822_) == 0 {
                                        v_isSharedCheck_4829_ =
                                            (!leanh::lean_is_exclusive(v___x_4822_)) as u8;
                                        if v_isSharedCheck_4829_ == 0 {
                                            v_unused_4830_ =
                                                leanh::lean_ctor_get(v___x_4822_, 0);
                                            leanh::lean_dec(v_unused_4830_);
                                            v___x_4824_ = v___x_4822_;
                                            v_isShared_4825_ = v_isSharedCheck_4829_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_4822_);
                                            v___x_4824_ = leanh::lean_box(0);
                                            v_isShared_4825_ = v_isSharedCheck_4829_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_4818_);
                                        v_a_4831_ = leanh::lean_ctor_get(v___x_4822_, 0);
                                        v_isSharedCheck_4838_ =
                                            (!leanh::lean_is_exclusive(v___x_4822_)) as u8;
                                        if v_isSharedCheck_4838_ == 0 {
                                            v___x_4833_ = v___x_4822_;
                                            v_isShared_4834_ = v_isSharedCheck_4838_;
                                            state = 5;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4831_);
                                            leanh::lean_dec(v___x_4822_);
                                            v___x_4833_ = leanh::lean_box(0);
                                            v_isShared_4834_ = v_isSharedCheck_4838_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4818_);
                                    leanh::lean_dec(v_a_4810_);
                                    return v___x_4819_;
                                }
                            } else {
                                leanh::lean_dec(v_a_4810_);
                                return v___x_4817_;
                            }
                        } else {
                            leanh::lean_dec(v_a_4808_);
                            leanh::lean_dec(v_a_4804_);
                            leanh::lean_dec(v_a_4795_);
                            leanh::lean_dec_ref(v_runInBase_4789_);
                            return v___x_4809_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4804_);
                        leanh::lean_dec(v_a_4795_);
                        leanh::lean_dec_ref(v_runInBase_4789_);
                        return v___x_4807_;
                    }
                } else {
                    leanh::lean_dec(v_a_4795_);
                    leanh::lean_dec_ref(v_runInBase_4789_);
                    return v___x_4803_;
                }
            }
            3 => {
                if v_isShared_4825_ == 0 {
                    leanh::lean_ctor_set(v___x_4824_, 0, v_a_4818_);
                    v___x_4827_ = v___x_4824_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4818_);
                    v___x_4827_ = v_reuseFailAlloc_4828_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4827_;
            }
            5 => {
                if v_isShared_4834_ == 0 {
                    v___x_4836_ = v___x_4833_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
                    v___x_4836_ = v_reuseFailAlloc_4837_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkContinue___boxed(
    mut v_base_4844_: *mut leanh::LeanObject,
    mut v_a_4845_: *mut leanh::LeanObject,
    mut v_a_4846_: *mut leanh::LeanObject,
    mut v_a_4847_: *mut leanh::LeanObject,
    mut v_a_4848_: *mut leanh::LeanObject,
    mut v_a_4849_: *mut leanh::LeanObject,
    mut v_a_4850_: *mut leanh::LeanObject,
    mut v_a_4851_: *mut leanh::LeanObject,
    mut v_a_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4853_ = l_Lean_Elab_Do_ControlStack_mkContinue(
        v_base_4844_,
        v_a_4845_,
        v_a_4846_,
        v_a_4847_,
        v_a_4848_,
        v_a_4849_,
        v_a_4850_,
        v_a_4851_,
    );
    leanh::lean_dec(v_a_4851_);
    leanh::lean_dec_ref(v_a_4850_);
    leanh::lean_dec(v_a_4849_);
    leanh::lean_dec_ref(v_a_4848_);
    leanh::lean_dec(v_a_4847_);
    leanh::lean_dec_ref(v_a_4846_);
    leanh::lean_dec_ref(v_a_4845_);
    return v_res_4853_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkReturn(
    mut v_base_4862_: *mut leanh::LeanObject,
    mut v_r_4863_: *mut leanh::LeanObject,
    mut v_a_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_a_4866_: *mut leanh::LeanObject,
    mut v_a_4867_: *mut leanh::LeanObject,
    mut v_a_4868_: *mut leanh::LeanObject,
    mut v_a_4869_: *mut leanh::LeanObject,
    mut v_a_4870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_m_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_runInBase_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4876_: u8 = 0;
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnit_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnitUnit_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: u8 = 0;
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4913_: u8 = 0;
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4917_: u8 = 0;
    let mut v_reuseFailAlloc_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4919_: u8 = 0;
    let mut v_unused_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_m_4872_ = leanh::lean_ctor_get(v_base_4862_, 1);
                v_runInBase_4873_ = leanh::lean_ctor_get(v_base_4862_, 3);
                v_isSharedCheck_4919_ = (!leanh::lean_is_exclusive(v_base_4862_)) as u8;
                if v_isSharedCheck_4919_ == 0 {
                    v_unused_4920_ = leanh::lean_ctor_get(v_base_4862_, 4);
                    leanh::lean_dec(v_unused_4920_);
                    v_unused_4921_ = leanh::lean_ctor_get(v_base_4862_, 2);
                    leanh::lean_dec(v_unused_4921_);
                    v_unused_4922_ = leanh::lean_ctor_get(v_base_4862_, 0);
                    leanh::lean_dec(v_unused_4922_);
                    v___x_4875_ = v_base_4862_;
                    v_isShared_4876_ = v_isSharedCheck_4919_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_runInBase_4873_);
                    leanh::lean_inc(v_m_4872_);
                    leanh::lean_dec(v_base_4862_);
                    v___x_4875_ = leanh::lean_box(0);
                    v_isShared_4876_ = v_isSharedCheck_4919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_4870_);
                leanh::lean_inc_ref(v_a_4869_);
                leanh::lean_inc(v_a_4868_);
                leanh::lean_inc_ref(v_a_4867_);
                leanh::lean_inc(v_a_4866_);
                leanh::lean_inc_ref(v_a_4865_);
                leanh::lean_inc_ref(v_a_4864_);
                v___x_4877_ = leanh::lean_apply_8(
                    v_m_4872_,
                    v_a_4864_,
                    v_a_4865_,
                    v_a_4866_,
                    v_a_4867_,
                    v_a_4868_,
                    v_a_4869_,
                    v_a_4870_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4877_) == 0 {
                    v_monadInfo_4878_ = leanh::lean_ctor_get(v_a_4864_, 0);
                    v_a_4879_ = leanh::lean_ctor_get(v___x_4877_, 0);
                    leanh::lean_inc_n(v_a_4879_, 2);
                    leanh::lean_dec_ref_known(v___x_4877_, 1);
                    v_doBlockResultType_4880_ = leanh::lean_ctor_get(v_a_4864_, 3);
                    v_u_4881_ = leanh::lean_ctor_get(v_monadInfo_4878_, 1);
                    v_v_4882_ = leanh::lean_ctor_get(v_monadInfo_4878_, 2);
                    v_cachedPUnit_4883_ = leanh::lean_ctor_get(v_monadInfo_4878_, 3);
                    v_cachedPUnitUnit_4884_ = leanh::lean_ctor_get(v_monadInfo_4878_, 4);
                    leanh::lean_inc_ref(v_cachedPUnitUnit_4884_);
                    leanh::lean_inc_ref(v_cachedPUnit_4883_);
                    leanh::lean_inc(v_v_4882_);
                    leanh::lean_inc(v_u_4881_);
                    if v_isShared_4876_ == 0 {
                        leanh::lean_ctor_set(v___x_4875_, 4, v_cachedPUnitUnit_4884_);
                        leanh::lean_ctor_set(v___x_4875_, 3, v_cachedPUnit_4883_);
                        leanh::lean_ctor_set(v___x_4875_, 2, v_v_4882_);
                        leanh::lean_ctor_set(v___x_4875_, 1, v_u_4881_);
                        leanh::lean_ctor_set(v___x_4875_, 0, v_a_4879_);
                        v___x_4886_ = v___x_4875_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4918_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4879_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 1, v_u_4881_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 2, v_v_4882_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 3, v_cachedPUnit_4883_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_4918_,
                            4,
                            v_cachedPUnitUnit_4884_,
                        );
                        v___x_4886_ = v_reuseFailAlloc_4918_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4875_);
                    leanh::lean_dec_ref(v_runInBase_4873_);
                    leanh::lean_dec_ref(v_r_4863_);
                    return v___x_4877_;
                }
            }
            2 => {
                v___x_4887_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(
                    v___x_4886_,
                    v_a_4865_,
                    v_a_4866_,
                    v_a_4867_,
                    v_a_4868_,
                    v_a_4869_,
                    v_a_4870_,
                );
                if leanh::lean_obj_tag(v___x_4887_) == 0 {
                    v_a_4888_ = leanh::lean_ctor_get(v___x_4887_, 0);
                    leanh::lean_inc(v_a_4888_);
                    leanh::lean_dec_ref_known(v___x_4887_, 1);
                    leanh::lean_inc(v_a_4870_);
                    leanh::lean_inc_ref(v_a_4869_);
                    leanh::lean_inc(v_a_4868_);
                    leanh::lean_inc_ref(v_a_4867_);
                    leanh::lean_inc_ref(v_r_4863_);
                    v___x_4889_ =
                        lean_infer_type(v_r_4863_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
                    if leanh::lean_obj_tag(v___x_4889_) == 0 {
                        v_a_4890_ = leanh::lean_ctor_get(v___x_4889_, 0);
                        leanh::lean_inc(v_a_4890_);
                        leanh::lean_dec_ref_known(v___x_4889_, 1);
                        v___x_4891_ = l_Lean_Elab_Do_ControlStack_mkReturn___closed__1;
                        v___x_4892_ = 0;
                        v___x_4893_ = l_Lean_Elab_Do_mkFreshResultType___redArg(
                            v___x_4891_,
                            v___x_4892_,
                            v_a_4864_,
                            v_a_4867_,
                            v_a_4868_,
                            v_a_4869_,
                            v_a_4870_,
                        );
                        if leanh::lean_obj_tag(v___x_4893_) == 0 {
                            v_a_4894_ = leanh::lean_ctor_get(v___x_4893_, 0);
                            leanh::lean_inc(v_a_4894_);
                            leanh::lean_dec_ref_known(v___x_4893_, 1);
                            leanh::lean_inc_ref(v_doBlockResultType_4880_);
                            v___x_4895_ = l_Lean_Elab_Do_mkMonadApp(
                                v_doBlockResultType_4880_,
                                v_a_4864_,
                                v_a_4865_,
                                v_a_4866_,
                                v_a_4867_,
                                v_a_4868_,
                                v_a_4869_,
                                v_a_4870_,
                            );
                            if leanh::lean_obj_tag(v___x_4895_) == 0 {
                                v_a_4896_ = leanh::lean_ctor_get(v___x_4895_, 0);
                                leanh::lean_inc(v_a_4896_);
                                leanh::lean_dec_ref_known(v___x_4895_, 1);
                                v___x_4897_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_exceptT_stM___closed__1;
                                v___x_4898_ = leanh::lean_box(0);
                                leanh::lean_inc(v_v_4882_);
                                v___x_4899_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4899_, 0, v_v_4882_);
                                leanh::lean_ctor_set(v___x_4899_, 1, v___x_4898_);
                                leanh::lean_inc(v_u_4881_);
                                v___x_4900_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4900_, 0, v_u_4881_);
                                leanh::lean_ctor_set(v___x_4900_, 1, v___x_4899_);
                                leanh::lean_inc_ref(v___x_4900_);
                                v___x_4901_ = l_Lean_mkConst(v___x_4897_, v___x_4900_);
                                leanh::lean_inc(v_a_4894_);
                                leanh::lean_inc(v_a_4890_);
                                v___x_4902_ = l_Lean_mkAppB(v___x_4901_, v_a_4890_, v_a_4894_);
                                leanh::lean_inc(v_a_4879_);
                                v___x_4903_ = l_Lean_Expr_app___override(v_a_4879_, v___x_4902_);
                                v___x_4904_ = l_Lean_Elab_Do_ControlStack_mkReturn___closed__2;
                                v___x_4905_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_synthUsingDefEq___redArg(v___x_4904_, v_a_4896_, v___x_4903_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_);
                                if leanh::lean_obj_tag(v___x_4905_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4905_, 1);
                                    v___x_4906_ = l_Lean_Elab_Do_ControlStack_mkReturn___closed__4;
                                    v___x_4907_ = l_Lean_mkConst(v___x_4906_, v___x_4900_);
                                    v___x_4908_ = l_Lean_mkApp5(
                                        v___x_4907_,
                                        v_a_4890_,
                                        v_a_4879_,
                                        v_a_4894_,
                                        v_a_4888_,
                                        v_r_4863_,
                                    );
                                    leanh::lean_inc(v_a_4870_);
                                    leanh::lean_inc_ref(v_a_4869_);
                                    leanh::lean_inc(v_a_4868_);
                                    leanh::lean_inc_ref(v_a_4867_);
                                    leanh::lean_inc(v_a_4866_);
                                    leanh::lean_inc_ref(v_a_4865_);
                                    leanh::lean_inc_ref(v_a_4864_);
                                    v___x_4909_ = leanh::lean_apply_9(
                                        v_runInBase_4873_,
                                        v___x_4908_,
                                        v_a_4864_,
                                        v_a_4865_,
                                        v_a_4866_,
                                        v_a_4867_,
                                        v_a_4868_,
                                        v_a_4869_,
                                        v_a_4870_,
                                        leanh::lean_box(0),
                                    );
                                    return v___x_4909_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_4900_, 2);
                                    leanh::lean_dec(v_a_4894_);
                                    leanh::lean_dec(v_a_4890_);
                                    leanh::lean_dec(v_a_4888_);
                                    leanh::lean_dec(v_a_4879_);
                                    leanh::lean_dec_ref(v_runInBase_4873_);
                                    leanh::lean_dec_ref(v_r_4863_);
                                    v_a_4910_ = leanh::lean_ctor_get(v___x_4905_, 0);
                                    v_isSharedCheck_4917_ =
                                        (!leanh::lean_is_exclusive(v___x_4905_)) as u8;
                                    if v_isSharedCheck_4917_ == 0 {
                                        v___x_4912_ = v___x_4905_;
                                        v_isShared_4913_ = v_isSharedCheck_4917_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4910_);
                                        leanh::lean_dec(v___x_4905_);
                                        v___x_4912_ = leanh::lean_box(0);
                                        v_isShared_4913_ = v_isSharedCheck_4917_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_4894_);
                                leanh::lean_dec(v_a_4890_);
                                leanh::lean_dec(v_a_4888_);
                                leanh::lean_dec(v_a_4879_);
                                leanh::lean_dec_ref(v_runInBase_4873_);
                                leanh::lean_dec_ref(v_r_4863_);
                                return v___x_4895_;
                            }
                        } else {
                            leanh::lean_dec(v_a_4890_);
                            leanh::lean_dec(v_a_4888_);
                            leanh::lean_dec(v_a_4879_);
                            leanh::lean_dec_ref(v_runInBase_4873_);
                            leanh::lean_dec_ref(v_r_4863_);
                            return v___x_4893_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4888_);
                        leanh::lean_dec(v_a_4879_);
                        leanh::lean_dec_ref(v_runInBase_4873_);
                        leanh::lean_dec_ref(v_r_4863_);
                        return v___x_4889_;
                    }
                } else {
                    leanh::lean_dec(v_a_4879_);
                    leanh::lean_dec_ref(v_runInBase_4873_);
                    leanh::lean_dec_ref(v_r_4863_);
                    return v___x_4887_;
                }
            }
            3 => {
                if v_isShared_4913_ == 0 {
                    v___x_4915_ = v___x_4912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4916_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
                    v___x_4915_ = v_reuseFailAlloc_4916_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkReturn___boxed(
    mut v_base_4923_: *mut leanh::LeanObject,
    mut v_r_4924_: *mut leanh::LeanObject,
    mut v_a_4925_: *mut leanh::LeanObject,
    mut v_a_4926_: *mut leanh::LeanObject,
    mut v_a_4927_: *mut leanh::LeanObject,
    mut v_a_4928_: *mut leanh::LeanObject,
    mut v_a_4929_: *mut leanh::LeanObject,
    mut v_a_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4933_ = l_Lean_Elab_Do_ControlStack_mkReturn(
        v_base_4923_,
        v_r_4924_,
        v_a_4925_,
        v_a_4926_,
        v_a_4927_,
        v_a_4928_,
        v_a_4929_,
        v_a_4930_,
        v_a_4931_,
    );
    leanh::lean_dec(v_a_4931_);
    leanh::lean_dec_ref(v_a_4930_);
    leanh::lean_dec(v_a_4929_);
    leanh::lean_dec_ref(v_a_4928_);
    leanh::lean_dec(v_a_4927_);
    leanh::lean_dec_ref(v_a_4926_);
    leanh::lean_dec_ref(v_a_4925_);
    return v_res_4933_;
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkPure(
    mut v_base_4948_: *mut leanh::LeanObject,
    mut v_resultName_4949_: *mut leanh::LeanObject,
    mut v_a_4950_: *mut leanh::LeanObject,
    mut v_a_4951_: *mut leanh::LeanObject,
    mut v_a_4952_: *mut leanh::LeanObject,
    mut v_a_4953_: *mut leanh::LeanObject,
    mut v_a_4954_: *mut leanh::LeanObject,
    mut v_a_4955_: *mut leanh::LeanObject,
    mut v_a_4956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_m_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_runInBase_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4962_: u8 = 0;
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnit_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cachedPUnitUnit_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut v_unused_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_m_4958_ = leanh::lean_ctor_get(v_base_4948_, 1);
                v_runInBase_4959_ = leanh::lean_ctor_get(v_base_4948_, 3);
                v_isSharedCheck_4992_ = (!leanh::lean_is_exclusive(v_base_4948_)) as u8;
                if v_isSharedCheck_4992_ == 0 {
                    v_unused_4993_ = leanh::lean_ctor_get(v_base_4948_, 4);
                    leanh::lean_dec(v_unused_4993_);
                    v_unused_4994_ = leanh::lean_ctor_get(v_base_4948_, 2);
                    leanh::lean_dec(v_unused_4994_);
                    v_unused_4995_ = leanh::lean_ctor_get(v_base_4948_, 0);
                    leanh::lean_dec(v_unused_4995_);
                    v___x_4961_ = v_base_4948_;
                    v_isShared_4962_ = v_isSharedCheck_4992_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_runInBase_4959_);
                    leanh::lean_inc(v_m_4958_);
                    leanh::lean_dec(v_base_4948_);
                    v___x_4961_ = leanh::lean_box(0);
                    v_isShared_4962_ = v_isSharedCheck_4992_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_4956_);
                leanh::lean_inc_ref(v_a_4955_);
                leanh::lean_inc(v_a_4954_);
                leanh::lean_inc_ref(v_a_4953_);
                leanh::lean_inc(v_a_4952_);
                leanh::lean_inc_ref(v_a_4951_);
                leanh::lean_inc_ref(v_a_4950_);
                v___x_4963_ = leanh::lean_apply_8(
                    v_m_4958_,
                    v_a_4950_,
                    v_a_4951_,
                    v_a_4952_,
                    v_a_4953_,
                    v_a_4954_,
                    v_a_4955_,
                    v_a_4956_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4963_) == 0 {
                    v_monadInfo_4964_ = leanh::lean_ctor_get(v_a_4950_, 0);
                    v_a_4965_ = leanh::lean_ctor_get(v___x_4963_, 0);
                    leanh::lean_inc_n(v_a_4965_, 2);
                    leanh::lean_dec_ref_known(v___x_4963_, 1);
                    v_u_4966_ = leanh::lean_ctor_get(v_monadInfo_4964_, 1);
                    v_v_4967_ = leanh::lean_ctor_get(v_monadInfo_4964_, 2);
                    v_cachedPUnit_4968_ = leanh::lean_ctor_get(v_monadInfo_4964_, 3);
                    v_cachedPUnitUnit_4969_ = leanh::lean_ctor_get(v_monadInfo_4964_, 4);
                    leanh::lean_inc_ref(v_cachedPUnitUnit_4969_);
                    leanh::lean_inc_ref(v_cachedPUnit_4968_);
                    leanh::lean_inc(v_v_4967_);
                    leanh::lean_inc(v_u_4966_);
                    if v_isShared_4962_ == 0 {
                        leanh::lean_ctor_set(v___x_4961_, 4, v_cachedPUnitUnit_4969_);
                        leanh::lean_ctor_set(v___x_4961_, 3, v_cachedPUnit_4968_);
                        leanh::lean_ctor_set(v___x_4961_, 2, v_v_4967_);
                        leanh::lean_ctor_set(v___x_4961_, 1, v_u_4966_);
                        leanh::lean_ctor_set(v___x_4961_, 0, v_a_4965_);
                        v___x_4971_ = v___x_4961_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4991_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4965_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 1, v_u_4966_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 2, v_v_4967_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 3, v_cachedPUnit_4968_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_4991_,
                            4,
                            v_cachedPUnitUnit_4969_,
                        );
                        v___x_4971_ = v_reuseFailAlloc_4991_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4961_);
                    leanh::lean_dec_ref(v_runInBase_4959_);
                    leanh::lean_dec(v_resultName_4949_);
                    return v___x_4963_;
                }
            }
            2 => {
                v___x_4972_ = l___private_Lean_Elab_Do_Control_0__Lean_Elab_Do_mkInstMonad(
                    v___x_4971_,
                    v_a_4951_,
                    v_a_4952_,
                    v_a_4953_,
                    v_a_4954_,
                    v_a_4955_,
                    v_a_4956_,
                );
                if leanh::lean_obj_tag(v___x_4972_) == 0 {
                    v_a_4973_ = leanh::lean_ctor_get(v___x_4972_, 0);
                    leanh::lean_inc(v_a_4973_);
                    leanh::lean_dec_ref_known(v___x_4972_, 1);
                    v___x_4974_ = l_Lean_Meta_getFVarFromUserName(
                        v_resultName_4949_,
                        v_a_4953_,
                        v_a_4954_,
                        v_a_4955_,
                        v_a_4956_,
                    );
                    if leanh::lean_obj_tag(v___x_4974_) == 0 {
                        v_a_4975_ = leanh::lean_ctor_get(v___x_4974_, 0);
                        leanh::lean_inc_n(v_a_4975_, 2);
                        leanh::lean_dec_ref_known(v___x_4974_, 1);
                        leanh::lean_inc(v_a_4956_);
                        leanh::lean_inc_ref(v_a_4955_);
                        leanh::lean_inc(v_a_4954_);
                        leanh::lean_inc_ref(v_a_4953_);
                        v___x_4976_ =
                            lean_infer_type(v_a_4975_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_);
                        if leanh::lean_obj_tag(v___x_4976_) == 0 {
                            v_a_4977_ = leanh::lean_ctor_get(v___x_4976_, 0);
                            leanh::lean_inc(v_a_4977_);
                            leanh::lean_dec_ref_known(v___x_4976_, 1);
                            v___x_4978_ = l_Lean_Elab_Do_ControlStack_mkPure___closed__2;
                            v___x_4979_ = leanh::lean_box(0);
                            leanh::lean_inc(v_v_4967_);
                            v___x_4980_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4980_, 0, v_v_4967_);
                            leanh::lean_ctor_set(v___x_4980_, 1, v___x_4979_);
                            leanh::lean_inc(v_u_4966_);
                            v___x_4981_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4981_, 0, v_u_4966_);
                            leanh::lean_ctor_set(v___x_4981_, 1, v___x_4980_);
                            leanh::lean_inc_ref_n(v___x_4981_, 2);
                            v___x_4982_ = l_Lean_mkConst(v___x_4978_, v___x_4981_);
                            v___x_4983_ = l_Lean_Elab_Do_ControlStack_mkPure___closed__4;
                            v___x_4984_ = l_Lean_mkConst(v___x_4983_, v___x_4981_);
                            leanh::lean_inc_n(v_a_4965_, 2);
                            v___x_4985_ = l_Lean_mkAppB(v___x_4984_, v_a_4965_, v_a_4973_);
                            v___x_4986_ = l_Lean_mkAppB(v___x_4982_, v_a_4965_, v___x_4985_);
                            v___x_4987_ = l_Lean_Elab_Do_ControlStack_mkPure___closed__7;
                            v___x_4988_ = l_Lean_mkConst(v___x_4987_, v___x_4981_);
                            v___x_4989_ = l_Lean_mkApp4(
                                v___x_4988_,
                                v_a_4965_,
                                v___x_4986_,
                                v_a_4977_,
                                v_a_4975_,
                            );
                            leanh::lean_inc(v_a_4956_);
                            leanh::lean_inc_ref(v_a_4955_);
                            leanh::lean_inc(v_a_4954_);
                            leanh::lean_inc_ref(v_a_4953_);
                            leanh::lean_inc(v_a_4952_);
                            leanh::lean_inc_ref(v_a_4951_);
                            leanh::lean_inc_ref(v_a_4950_);
                            v___x_4990_ = leanh::lean_apply_9(
                                v_runInBase_4959_,
                                v___x_4989_,
                                v_a_4950_,
                                v_a_4951_,
                                v_a_4952_,
                                v_a_4953_,
                                v_a_4954_,
                                v_a_4955_,
                                v_a_4956_,
                                leanh::lean_box(0),
                            );
                            return v___x_4990_;
                        } else {
                            leanh::lean_dec(v_a_4975_);
                            leanh::lean_dec(v_a_4973_);
                            leanh::lean_dec(v_a_4965_);
                            leanh::lean_dec_ref(v_runInBase_4959_);
                            return v___x_4976_;
                        }
                    } else {
                        leanh::lean_dec(v_a_4973_);
                        leanh::lean_dec(v_a_4965_);
                        leanh::lean_dec_ref(v_runInBase_4959_);
                        return v___x_4974_;
                    }
                } else {
                    leanh::lean_dec(v_a_4965_);
                    leanh::lean_dec_ref(v_runInBase_4959_);
                    leanh::lean_dec(v_resultName_4949_);
                    return v___x_4972_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlStack_mkPure___boxed(
    mut v_base_4996_: *mut leanh::LeanObject,
    mut v_resultName_4997_: *mut leanh::LeanObject,
    mut v_a_4998_: *mut leanh::LeanObject,
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_a_5000_: *mut leanh::LeanObject,
    mut v_a_5001_: *mut leanh::LeanObject,
    mut v_a_5002_: *mut leanh::LeanObject,
    mut v_a_5003_: *mut leanh::LeanObject,
    mut v_a_5004_: *mut leanh::LeanObject,
    mut v_a_5005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5006_ = l_Lean_Elab_Do_ControlStack_mkPure(
        v_base_4996_,
        v_resultName_4997_,
        v_a_4998_,
        v_a_4999_,
        v_a_5000_,
        v_a_5001_,
        v_a_5002_,
        v_a_5003_,
        v_a_5004_,
    );
    leanh::lean_dec(v_a_5004_);
    leanh::lean_dec_ref(v_a_5003_);
    leanh::lean_dec(v_a_5002_);
    leanh::lean_dec_ref(v_a_5001_);
    leanh::lean_dec(v_a_5000_);
    leanh::lean_dec_ref(v_a_4999_);
    leanh::lean_dec_ref(v_a_4998_);
    return v_res_5006_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(
    mut v_info_5007_: *mut leanh::LeanObject,
    mut v_as_5008_: *mut leanh::LeanObject,
    mut v_i_5009_: usize,
    mut v_stop_5010_: usize,
    mut v_b_5011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: usize = 0;
    let mut v___x_5015_: usize = 0;
    let mut v___x_5017_: u8 = 0;
    let mut v_reassigns_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: u8 = 0;
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5017_ = lean_usize_dec_eq(v_i_5009_, v_stop_5010_);
                if v___x_5017_ == 0 {
                    v_reassigns_5018_ = leanh::lean_ctor_get(v_info_5007_, 1);
                    v___x_5019_ = lean_array_uget_borrowed(v_as_5008_, v_i_5009_);
                    v___x_5020_ = l_Lean_TSyntax_getId(v___x_5019_);
                    v___x_5021_ = l_Lean_NameSet_contains(v_reassigns_5018_, v___x_5020_);
                    leanh::lean_dec(v___x_5020_);
                    if v___x_5021_ == 0 {
                        v___y_5013_ = v_b_5011_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_5019_);
                        v___x_5022_ = lean_array_push(v_b_5011_, v___x_5019_);
                        v___y_5013_ = v___x_5022_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5011_;
                }
            }
            1 => {
                v___x_5014_ = 1usize;
                v___x_5015_ = lean_usize_add(v_i_5009_, v___x_5014_);
                v_i_5009_ = v___x_5015_;
                v_b_5011_ = v___y_5013_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0___boxed(
    mut v_info_5023_: *mut leanh::LeanObject,
    mut v_as_5024_: *mut leanh::LeanObject,
    mut v_i_5025_: *mut leanh::LeanObject,
    mut v_stop_5026_: *mut leanh::LeanObject,
    mut v_b_5027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5028_: usize = 0;
    let mut v_stop_boxed_5029_: usize = 0;
    let mut v_res_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5028_ = leanh::lean_unbox_usize(v_i_5025_);
    leanh::lean_dec(v_i_5025_);
    v_stop_boxed_5029_ = leanh::lean_unbox_usize(v_stop_5026_);
    leanh::lean_dec(v_stop_5026_);
    v_res_5030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(v_info_5023_, v_as_5024_, v_i_boxed_5028_, v_stop_boxed_5029_, v_b_5027_);
    leanh::lean_dec_ref(v_as_5024_);
    leanh::lean_dec_ref(v_info_5023_);
    return v_res_5030_;
}
pub unsafe fn l_Lean_Elab_Do_ControlLifter_ofCont(
    mut v_info_5033_: *mut leanh::LeanObject,
    mut v_dec_5034_: *mut leanh::LeanObject,
    mut v_a_5035_: *mut leanh::LeanObject,
    mut v_a_5036_: *mut leanh::LeanObject,
    mut v_a_5037_: *mut leanh::LeanObject,
    mut v_a_5038_: *mut leanh::LeanObject,
    mut v_a_5039_: *mut leanh::LeanObject,
    mut v_a_5040_: *mut leanh::LeanObject,
    mut v_a_5041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5049_: u8 = 0;
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_continueBase_x3f_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_controlStack_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stM_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noFallthrough_5067_: u8 = 0;
    let mut v_a_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: u8 = 0;
    let mut v_a_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u8 = 0;
    let mut v_a_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5079_: u8 = 0;
    let mut v_monadInfo_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVars_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5084_: u8 = 0;
    let mut v___y_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_breakBase_x3f_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_controlStack_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5098_: u8 = 0;
    let mut v___y_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5100_: u8 = 0;
    let mut v___y_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_controlStack_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5114_: u8 = 0;
    let mut v___y_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5116_: u8 = 0;
    let mut v_returnBase_x3f_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_controlStack_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5131_: u8 = 0;
    let mut v___y_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5133_: u8 = 0;
    let mut v___y_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5140_: u8 = 0;
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5145_: u8 = 0;
    let mut v___y_5147_: u8 = 0;
    let mut v___y_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5151_: u8 = 0;
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: u8 = 0;
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5162_: u8 = 0;
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_continues_5164_: u8 = 0;
    let mut v_a_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: u8 = 0;
    let mut v_a_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5170_: u8 = 0;
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5174_: u8 = 0;
    let mut v___y_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: u8 = 0;
    let mut v___y_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_breaks_5185_: u8 = 0;
    let mut v_a_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut v___y_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5199_: usize = 0;
    let mut v___x_5200_: usize = 0;
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5202_: usize = 0;
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_returnsEarly_5207_: u8 = 0;
    let mut v_a_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5220_: u8 = 0;
    let mut v_a_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5224_: u8 = 0;
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5228_: u8 = 0;
    let mut v_a_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5232_: u8 = 0;
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5236_: u8 = 0;
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: u8 = 0;
    let mut v___x_5241_: u8 = 0;
    let mut v___x_5242_: usize = 0;
    let mut v___x_5243_: usize = 0;
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: usize = 0;
    let mut v___x_5246_: usize = 0;
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_monadInfo_5080_ = leanh::lean_ctor_get(v_a_5035_, 0);
                v_mutVars_5081_ = leanh::lean_ctor_get(v_a_5035_, 1);
                v___x_5237_ = leanh::lean_unsigned_to_nat(0);
                v___x_5238_ = lean_array_get_size(v_mutVars_5081_);
                v___x_5239_ = l_Lean_Elab_Do_ControlLifter_ofCont___closed__0;
                v___x_5240_ = lean_nat_dec_lt(v___x_5237_, v___x_5238_);
                if v___x_5240_ == 0 {
                    v___y_5196_ = v___x_5239_;
                    state = 19;
                    continue;
                } else {
                    v___x_5241_ = lean_nat_dec_le(v___x_5238_, v___x_5238_);
                    if v___x_5241_ == 0 {
                        if v___x_5240_ == 0 {
                            v___y_5196_ = v___x_5239_;
                            state = 19;
                            continue;
                        } else {
                            v___x_5242_ = 0usize;
                            v___x_5243_ = lean_usize_of_nat(v___x_5238_);
                            v___x_5244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(v_info_5033_, v_mutVars_5081_, v___x_5242_, v___x_5243_, v___x_5239_);
                            v___y_5196_ = v___x_5244_;
                            state = 19;
                            continue;
                        }
                    } else {
                        v___x_5245_ = 0usize;
                        v___x_5246_ = lean_usize_of_nat(v___x_5238_);
                        v___x_5247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_ControlLifter_ofCont_spec__0(v_info_5033_, v_mutVars_5081_, v___x_5245_, v___x_5246_, v___x_5239_);
                        v___y_5196_ = v___x_5247_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5050_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                leanh::lean_ctor_set(v___x_5050_, 0, v_dec_5034_);
                leanh::lean_ctor_set(v___x_5050_, 1, v___y_5048_);
                leanh::lean_ctor_set(v___x_5050_, 2, v___y_5045_);
                leanh::lean_ctor_set(v___x_5050_, 3, v___y_5046_);
                leanh::lean_ctor_set(v___x_5050_, 4, v___y_5047_);
                leanh::lean_ctor_set(v___x_5050_, 5, v___y_5044_);
                leanh::lean_ctor_set_uint8(
                    v___x_5050_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v___y_5049_,
                );
                v___x_5051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5051_, 0, v___x_5050_);
                return v___x_5051_;
            }
            2 => {
                v_stM_5064_ = leanh::lean_ctor_get(v_controlStack_5056_, 2);
                v_resultType_5065_ = leanh::lean_ctor_get(v_dec_5034_, 1);
                leanh::lean_inc_ref(v_stM_5064_);
                leanh::lean_inc(v___y_5063_);
                leanh::lean_inc_ref(v___y_5062_);
                leanh::lean_inc(v___y_5061_);
                leanh::lean_inc_ref(v___y_5060_);
                leanh::lean_inc(v___y_5059_);
                leanh::lean_inc_ref(v___y_5058_);
                leanh::lean_inc_ref(v___y_5057_);
                leanh::lean_inc_ref(v_resultType_5065_);
                v___x_5066_ = leanh::lean_apply_9(
                    v_stM_5064_,
                    v_resultType_5065_,
                    v___y_5057_,
                    v___y_5058_,
                    v___y_5059_,
                    v___y_5060_,
                    v___y_5061_,
                    v___y_5062_,
                    v___y_5063_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5066_) == 0 {
                    v_noFallthrough_5067_ = leanh::lean_ctor_get_uint8(
                        v_info_5033_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 3) as u32,
                    );
                    if v_noFallthrough_5067_ == 0 {
                        v_a_5068_ = leanh::lean_ctor_get(v___x_5066_, 0);
                        leanh::lean_inc(v_a_5068_);
                        leanh::lean_dec_ref_known(v___x_5066_, 1);
                        v___x_5069_ = 2;
                        v___y_5044_ = v_a_5068_;
                        v___y_5045_ = v___y_5053_;
                        v___y_5046_ = v_continueBase_x3f_5055_;
                        v___y_5047_ = v_controlStack_5056_;
                        v___y_5048_ = v___y_5054_;
                        v___y_5049_ = v___x_5069_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5070_ = leanh::lean_ctor_get(v___x_5066_, 0);
                        leanh::lean_inc(v_a_5070_);
                        leanh::lean_dec_ref_known(v___x_5066_, 1);
                        v___x_5071_ = 1;
                        v___y_5044_ = v_a_5070_;
                        v___y_5045_ = v___y_5053_;
                        v___y_5046_ = v_continueBase_x3f_5055_;
                        v___y_5047_ = v_controlStack_5056_;
                        v___y_5048_ = v___y_5054_;
                        v___y_5049_ = v___x_5071_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_controlStack_5056_);
                    leanh::lean_dec(v_continueBase_x3f_5055_);
                    leanh::lean_dec(v___y_5054_);
                    leanh::lean_dec(v___y_5053_);
                    leanh::lean_dec_ref(v_dec_5034_);
                    v_a_5072_ = leanh::lean_ctor_get(v___x_5066_, 0);
                    v_isSharedCheck_5079_ = (!leanh::lean_is_exclusive(v___x_5066_)) as u8;
                    if v_isSharedCheck_5079_ == 0 {
                        v___x_5074_ = v___x_5066_;
                        v_isShared_5075_ = v_isSharedCheck_5079_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5072_);
                        leanh::lean_dec(v___x_5066_);
                        v___x_5074_ = leanh::lean_box(0);
                        v_isShared_5075_ = v_isSharedCheck_5079_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5075_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
                    v___x_5077_ = v_reuseFailAlloc_5078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5077_;
            }
            5 => {
                if v___y_5084_ == 0 {
                    v___y_5053_ = v_breakBase_x3f_5086_;
                    v___y_5054_ = v___y_5085_;
                    v_continueBase_x3f_5055_ = v___y_5083_;
                    v_controlStack_5056_ = v_controlStack_5087_;
                    v___y_5057_ = v___y_5088_;
                    v___y_5058_ = v___y_5089_;
                    v___y_5059_ = v___y_5090_;
                    v___y_5060_ = v___y_5091_;
                    v___y_5061_ = v___y_5092_;
                    v___y_5062_ = v___y_5093_;
                    v___y_5063_ = v___y_5094_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_5083_);
                    leanh::lean_inc_ref(v_controlStack_5087_);
                    v___x_5095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5095_, 0, v_controlStack_5087_);
                    leanh::lean_inc_ref(v_monadInfo_5080_);
                    v___x_5096_ = l_Lean_Elab_Do_ControlStack_continueT(
                        v_monadInfo_5080_,
                        v_controlStack_5087_,
                    );
                    v___y_5053_ = v_breakBase_x3f_5086_;
                    v___y_5054_ = v___y_5085_;
                    v_continueBase_x3f_5055_ = v___x_5095_;
                    v_controlStack_5056_ = v___x_5096_;
                    v___y_5057_ = v___y_5088_;
                    v___y_5058_ = v___y_5089_;
                    v___y_5059_ = v___y_5090_;
                    v___y_5060_ = v___y_5091_;
                    v___y_5061_ = v___y_5092_;
                    v___y_5062_ = v___y_5093_;
                    v___y_5063_ = v___y_5094_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v___y_5098_ == 0 {
                    leanh::lean_inc(v___y_5099_);
                    v___y_5083_ = v___y_5099_;
                    v___y_5084_ = v___y_5100_;
                    v___y_5085_ = v___y_5101_;
                    v_breakBase_x3f_5086_ = v___y_5099_;
                    v_controlStack_5087_ = v_controlStack_5102_;
                    v___y_5088_ = v___y_5103_;
                    v___y_5089_ = v___y_5104_;
                    v___y_5090_ = v___y_5105_;
                    v___y_5091_ = v___y_5106_;
                    v___y_5092_ = v___y_5107_;
                    v___y_5093_ = v___y_5108_;
                    v___y_5094_ = v___y_5109_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_controlStack_5102_);
                    v___x_5110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5110_, 0, v_controlStack_5102_);
                    leanh::lean_inc_ref(v_monadInfo_5080_);
                    v___x_5111_ =
                        l_Lean_Elab_Do_ControlStack_breakT(v_monadInfo_5080_, v_controlStack_5102_);
                    v___y_5083_ = v___y_5099_;
                    v___y_5084_ = v___y_5100_;
                    v___y_5085_ = v___y_5101_;
                    v_breakBase_x3f_5086_ = v___x_5110_;
                    v_controlStack_5087_ = v___x_5111_;
                    v___y_5088_ = v___y_5103_;
                    v___y_5089_ = v___y_5104_;
                    v___y_5090_ = v___y_5105_;
                    v___y_5091_ = v___y_5106_;
                    v___y_5092_ = v___y_5107_;
                    v___y_5093_ = v___y_5108_;
                    v___y_5094_ = v___y_5109_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                if leanh::lean_obj_tag(v___y_5113_) == 1 {
                    v_val_5126_ = leanh::lean_ctor_get(v___y_5113_, 0);
                    leanh::lean_inc(v_val_5126_);
                    leanh::lean_dec_ref_known(v___y_5113_, 1);
                    v_fst_5127_ = leanh::lean_ctor_get(v_val_5126_, 0);
                    leanh::lean_inc(v_fst_5127_);
                    v_snd_5128_ = leanh::lean_ctor_get(v_val_5126_, 1);
                    leanh::lean_inc(v_snd_5128_);
                    leanh::lean_dec(v_val_5126_);
                    leanh::lean_inc_ref(v_monadInfo_5080_);
                    v___x_5129_ = l_Lean_Elab_Do_ControlStack_stateT(
                        v_monadInfo_5080_,
                        v_fst_5127_,
                        v_snd_5128_,
                        v_controlStack_5118_,
                    );
                    v___y_5098_ = v___y_5114_;
                    v___y_5099_ = v___y_5115_;
                    v___y_5100_ = v___y_5116_;
                    v___y_5101_ = v_returnBase_x3f_5117_;
                    v_controlStack_5102_ = v___x_5129_;
                    v___y_5103_ = v___y_5119_;
                    v___y_5104_ = v___y_5120_;
                    v___y_5105_ = v___y_5121_;
                    v___y_5106_ = v___y_5122_;
                    v___y_5107_ = v___y_5123_;
                    v___y_5108_ = v___y_5124_;
                    v___y_5109_ = v___y_5125_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v___y_5113_);
                    v___y_5098_ = v___y_5114_;
                    v___y_5099_ = v___y_5115_;
                    v___y_5100_ = v___y_5116_;
                    v___y_5101_ = v_returnBase_x3f_5117_;
                    v_controlStack_5102_ = v_controlStack_5118_;
                    v___y_5103_ = v___y_5119_;
                    v___y_5104_ = v___y_5120_;
                    v___y_5105_ = v___y_5121_;
                    v___y_5106_ = v___y_5122_;
                    v___y_5107_ = v___y_5123_;
                    v___y_5108_ = v___y_5124_;
                    v___y_5109_ = v___y_5125_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_5135_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_monadInfo_5080_);
                v___x_5136_ = l_Lean_Elab_Do_ControlStack_base(v_monadInfo_5080_);
                if leanh::lean_obj_tag(v___y_5132_) == 1 {
                    v_val_5137_ = leanh::lean_ctor_get(v___y_5132_, 0);
                    v_isSharedCheck_5145_ = (!leanh::lean_is_exclusive(v___y_5132_)) as u8;
                    if v_isSharedCheck_5145_ == 0 {
                        v___x_5139_ = v___y_5132_;
                        v_isShared_5140_ = v_isSharedCheck_5145_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5137_);
                        leanh::lean_dec(v___y_5132_);
                        v___x_5139_ = leanh::lean_box(0);
                        v_isShared_5140_ = v_isSharedCheck_5145_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_5132_);
                    v___y_5113_ = v___y_5134_;
                    v___y_5114_ = v___y_5131_;
                    v___y_5115_ = v___x_5135_;
                    v___y_5116_ = v___y_5133_;
                    v_returnBase_x3f_5117_ = v___x_5135_;
                    v_controlStack_5118_ = v___x_5136_;
                    v___y_5119_ = v_a_5035_;
                    v___y_5120_ = v_a_5036_;
                    v___y_5121_ = v_a_5037_;
                    v___y_5122_ = v_a_5038_;
                    v___y_5123_ = v_a_5039_;
                    v___y_5124_ = v_a_5040_;
                    v___y_5125_ = v_a_5041_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                leanh::lean_inc_ref(v___x_5136_);
                if v_isShared_5140_ == 0 {
                    leanh::lean_ctor_set(v___x_5139_, 0, v___x_5136_);
                    v___x_5142_ = v___x_5139_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5144_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5136_);
                    v___x_5142_ = v_reuseFailAlloc_5144_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                leanh::lean_inc_ref(v_monadInfo_5080_);
                v___x_5143_ = l_Lean_Elab_Do_ControlStack_earlyReturnT(
                    v_monadInfo_5080_,
                    v_val_5137_,
                    v___x_5136_,
                );
                v___y_5113_ = v___y_5134_;
                v___y_5114_ = v___y_5131_;
                v___y_5115_ = v___x_5135_;
                v___y_5116_ = v___y_5133_;
                v_returnBase_x3f_5117_ = v___x_5142_;
                v_controlStack_5118_ = v___x_5143_;
                v___y_5119_ = v_a_5035_;
                v___y_5120_ = v_a_5036_;
                v___y_5121_ = v_a_5037_;
                v___y_5122_ = v_a_5038_;
                v___y_5123_ = v_a_5039_;
                v___y_5124_ = v_a_5040_;
                v___y_5125_ = v_a_5041_;
                state = 7;
                continue;
            }
            11 => {
                v___x_5152_ = lean_array_get_size(v___y_5148_);
                v___x_5153_ = leanh::lean_unsigned_to_nat(0);
                v___x_5154_ = lean_nat_dec_eq(v___x_5152_, v___x_5153_);
                if v___x_5154_ == 0 {
                    v___x_5155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5155_, 0, v___y_5148_);
                    leanh::lean_ctor_set(v___x_5155_, 1, v___y_5149_);
                    v___x_5156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5156_, 0, v___x_5155_);
                    v___y_5131_ = v___y_5147_;
                    v___y_5132_ = v___y_5150_;
                    v___y_5133_ = v___y_5151_;
                    v___y_5134_ = v___x_5156_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_5149_);
                    leanh::lean_dec_ref(v___y_5148_);
                    v___x_5157_ = leanh::lean_box(0);
                    v___y_5131_ = v___y_5147_;
                    v___y_5132_ = v___y_5150_;
                    v___y_5133_ = v___y_5151_;
                    v___y_5134_ = v___x_5157_;
                    state = 8;
                    continue;
                }
            }
            12 => {
                v___x_5163_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_5035_);
                if leanh::lean_obj_tag(v___x_5163_) == 0 {
                    v_continues_5164_ = leanh::lean_ctor_get_uint8(
                        v_info_5033_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    if v_continues_5164_ == 0 {
                        leanh::lean_dec_ref_known(v___x_5163_, 1);
                        v___y_5147_ = v___y_5162_;
                        v___y_5148_ = v___y_5159_;
                        v___y_5149_ = v___y_5160_;
                        v___y_5150_ = v___y_5161_;
                        v___y_5151_ = v_continues_5164_;
                        state = 11;
                        continue;
                    } else {
                        v_a_5165_ = leanh::lean_ctor_get(v___x_5163_, 0);
                        leanh::lean_inc(v_a_5165_);
                        leanh::lean_dec_ref_known(v___x_5163_, 1);
                        if leanh::lean_obj_tag(v_a_5165_) == 0 {
                            v___x_5166_ = 0;
                            v___y_5147_ = v___y_5162_;
                            v___y_5148_ = v___y_5159_;
                            v___y_5149_ = v___y_5160_;
                            v___y_5150_ = v___y_5161_;
                            v___y_5151_ = v___x_5166_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_a_5165_, 1);
                            v___y_5147_ = v___y_5162_;
                            v___y_5148_ = v___y_5159_;
                            v___y_5149_ = v___y_5160_;
                            v___y_5150_ = v___y_5161_;
                            v___y_5151_ = v_continues_5164_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_5161_);
                    leanh::lean_dec_ref(v___y_5160_);
                    leanh::lean_dec_ref(v___y_5159_);
                    leanh::lean_dec_ref(v_dec_5034_);
                    v_a_5167_ = leanh::lean_ctor_get(v___x_5163_, 0);
                    v_isSharedCheck_5174_ = (!leanh::lean_is_exclusive(v___x_5163_)) as u8;
                    if v_isSharedCheck_5174_ == 0 {
                        v___x_5169_ = v___x_5163_;
                        v_isShared_5170_ = v_isSharedCheck_5174_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5167_);
                        leanh::lean_dec(v___x_5163_);
                        v___x_5169_ = leanh::lean_box(0);
                        v_isShared_5170_ = v_isSharedCheck_5174_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_5170_ == 0 {
                    v___x_5172_ = v___x_5169_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
                    v___x_5172_ = v_reuseFailAlloc_5173_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5172_;
            }
            15 => {
                v___x_5179_ = 0;
                v___y_5159_ = v___y_5176_;
                v___y_5160_ = v___y_5177_;
                v___y_5161_ = v___y_5178_;
                v___y_5162_ = v___x_5179_;
                state = 12;
                continue;
            }
            16 => {
                v___x_5184_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_5035_);
                if leanh::lean_obj_tag(v___x_5184_) == 0 {
                    v_breaks_5185_ = leanh::lean_ctor_get_uint8(
                        v_info_5033_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    if v_breaks_5185_ == 0 {
                        leanh::lean_dec_ref_known(v___x_5184_, 1);
                        v___y_5176_ = v___y_5181_;
                        v___y_5177_ = v___y_5182_;
                        v___y_5178_ = v___y_5183_;
                        state = 15;
                        continue;
                    } else {
                        v_a_5186_ = leanh::lean_ctor_get(v___x_5184_, 0);
                        leanh::lean_inc(v_a_5186_);
                        leanh::lean_dec_ref_known(v___x_5184_, 1);
                        if leanh::lean_obj_tag(v_a_5186_) == 0 {
                            v___y_5176_ = v___y_5181_;
                            v___y_5177_ = v___y_5182_;
                            v___y_5178_ = v___y_5183_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_a_5186_, 1);
                            v___y_5159_ = v___y_5181_;
                            v___y_5160_ = v___y_5182_;
                            v___y_5161_ = v___y_5183_;
                            v___y_5162_ = v_breaks_5185_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_5183_);
                    leanh::lean_dec_ref(v___y_5182_);
                    leanh::lean_dec_ref(v___y_5181_);
                    leanh::lean_dec_ref(v_dec_5034_);
                    v_a_5187_ = leanh::lean_ctor_get(v___x_5184_, 0);
                    v_isSharedCheck_5194_ = (!leanh::lean_is_exclusive(v___x_5184_)) as u8;
                    if v_isSharedCheck_5194_ == 0 {
                        v___x_5189_ = v___x_5184_;
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5187_);
                        leanh::lean_dec(v___x_5184_);
                        v___x_5189_ = leanh::lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_5190_ == 0 {
                    v___x_5192_ = v___x_5189_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5192_;
            }
            19 => {
                v___x_5197_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_5035_);
                if leanh::lean_obj_tag(v___x_5197_) == 0 {
                    v_a_5198_ = leanh::lean_ctor_get(v___x_5197_, 0);
                    leanh::lean_inc(v_a_5198_);
                    leanh::lean_dec_ref_known(v___x_5197_, 1);
                    v_sz_5199_ = lean_array_size(v___y_5196_);
                    v___x_5200_ = 0usize;
                    leanh::lean_inc_ref(v___y_5196_);
                    v___x_5201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_mutVarNames_spec__0(v_sz_5199_, v___x_5200_, v___y_5196_);
                    v_sz_5202_ = lean_array_size(v___x_5201_);
                    v___x_5203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Do_Control_0__Lean_Elab_Do_ControlStack_stateT_get_u03c3_spec__0___redArg(v_sz_5202_, v___x_5200_, v___x_5201_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
                    if leanh::lean_obj_tag(v___x_5203_) == 0 {
                        v_a_5204_ = leanh::lean_ctor_get(v___x_5203_, 0);
                        leanh::lean_inc(v_a_5204_);
                        leanh::lean_dec_ref_known(v___x_5203_, 1);
                        v_u_5205_ = leanh::lean_ctor_get(v_monadInfo_5080_, 1);
                        leanh::lean_inc(v_u_5205_);
                        v___x_5206_ = l_Lean_Meta_mkProdN(
                            v_a_5204_, v_u_5205_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_,
                        );
                        if leanh::lean_obj_tag(v___x_5206_) == 0 {
                            v_returnsEarly_5207_ = leanh::lean_ctor_get_uint8(
                                v_info_5033_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 2)
                                    as u32,
                            );
                            if v_returnsEarly_5207_ == 0 {
                                leanh::lean_dec(v_a_5198_);
                                v_a_5208_ = leanh::lean_ctor_get(v___x_5206_, 0);
                                leanh::lean_inc(v_a_5208_);
                                leanh::lean_dec_ref_known(v___x_5206_, 1);
                                v___x_5209_ = leanh::lean_box(0);
                                v___y_5181_ = v___y_5196_;
                                v___y_5182_ = v_a_5208_;
                                v___y_5183_ = v___x_5209_;
                                state = 16;
                                continue;
                            } else {
                                v_a_5210_ = leanh::lean_ctor_get(v___x_5206_, 0);
                                leanh::lean_inc(v_a_5210_);
                                leanh::lean_dec_ref_known(v___x_5206_, 1);
                                v_resultType_5211_ = leanh::lean_ctor_get(v_a_5198_, 0);
                                leanh::lean_inc_ref(v_resultType_5211_);
                                leanh::lean_dec(v_a_5198_);
                                v___x_5212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5212_, 0, v_resultType_5211_);
                                v___y_5181_ = v___y_5196_;
                                v___y_5182_ = v_a_5210_;
                                v___y_5183_ = v___x_5212_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5198_);
                            leanh::lean_dec_ref(v___y_5196_);
                            leanh::lean_dec_ref(v_dec_5034_);
                            v_a_5213_ = leanh::lean_ctor_get(v___x_5206_, 0);
                            v_isSharedCheck_5220_ =
                                (!leanh::lean_is_exclusive(v___x_5206_)) as u8;
                            if v_isSharedCheck_5220_ == 0 {
                                v___x_5215_ = v___x_5206_;
                                v_isShared_5216_ = v_isSharedCheck_5220_;
                                state = 20;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5213_);
                                leanh::lean_dec(v___x_5206_);
                                v___x_5215_ = leanh::lean_box(0);
                                v_isShared_5216_ = v_isSharedCheck_5220_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5198_);
                        leanh::lean_dec_ref(v___y_5196_);
                        leanh::lean_dec_ref(v_dec_5034_);
                        v_a_5221_ = leanh::lean_ctor_get(v___x_5203_, 0);
                        v_isSharedCheck_5228_ =
                            (!leanh::lean_is_exclusive(v___x_5203_)) as u8;
                        if v_isSharedCheck_5228_ == 0 {
                            v___x_5223_ = v___x_5203_;
                            v_isShared_5224_ = v_isSharedCheck_5228_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5221_);
                            leanh::lean_dec(v___x_5203_);
                            v___x_5223_ = leanh::lean_box(0);
                            v_isShared_5224_ = v_isSharedCheck_5228_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_5196_);
                    leanh::lean_dec_ref(v_dec_5034_);
                    v_a_5229_ = leanh::lean_ctor_get(v___x_5197_, 0);
                    v_isSharedCheck_5236_ = (!leanh::lean_is_exclusive(v___x_5197_)) as u8;
                    if v_isSharedCheck_5236_ == 0 {
                        v___x_5231_ = v___x_5197_;
                        v_isShared_5232_ = v_isSharedCheck_5236_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5229_);
                        leanh::lean_dec(v___x_5197_);
                        v___x_5231_ = leanh::lean_box(0);
                        v_isShared_5232_ = v_isSharedCheck_5236_;
                        state = 24;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_5216_ == 0 {
                    v___x_5218_ = v___x_5215_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
                    v___x_5218_ = v_reuseFailAlloc_5219_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5218_;
            }
            22 => {
                if v_isShared_5224_ == 0 {
                    v___x_5226_ = v___x_5223_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
                    v___x_5226_ = v_reuseFailAlloc_5227_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5226_;
            }
            24 => {
                if v_isShared_5232_ == 0 {
                    v___x_5234_ = v___x_5231_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5235_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_a_5229_);
                    v___x_5234_ = v_reuseFailAlloc_5235_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_5234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlLifter_ofCont___boxed(
    mut v_info_5248_: *mut leanh::LeanObject,
    mut v_dec_5249_: *mut leanh::LeanObject,
    mut v_a_5250_: *mut leanh::LeanObject,
    mut v_a_5251_: *mut leanh::LeanObject,
    mut v_a_5252_: *mut leanh::LeanObject,
    mut v_a_5253_: *mut leanh::LeanObject,
    mut v_a_5254_: *mut leanh::LeanObject,
    mut v_a_5255_: *mut leanh::LeanObject,
    mut v_a_5256_: *mut leanh::LeanObject,
    mut v_a_5257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5258_ = l_Lean_Elab_Do_ControlLifter_ofCont(
        v_info_5248_,
        v_dec_5249_,
        v_a_5250_,
        v_a_5251_,
        v_a_5252_,
        v_a_5253_,
        v_a_5254_,
        v_a_5255_,
        v_a_5256_,
    );
    leanh::lean_dec(v_a_5256_);
    leanh::lean_dec_ref(v_a_5255_);
    leanh::lean_dec(v_a_5254_);
    leanh::lean_dec_ref(v_a_5253_);
    leanh::lean_dec(v_a_5252_);
    leanh::lean_dec_ref(v_a_5251_);
    leanh::lean_dec_ref(v_a_5250_);
    leanh::lean_dec_ref(v_info_5248_);
    return v_res_5258_;
}
pub unsafe fn l_Lean_Elab_Do_ControlLifter_lift(
    mut v_l_5259_: *mut leanh::LeanObject,
    mut v_elabElem_5260_: *mut leanh::LeanObject,
    mut v_a_5261_: *mut leanh::LeanObject,
    mut v_a_5262_: *mut leanh::LeanObject,
    mut v_a_5263_: *mut leanh::LeanObject,
    mut v_a_5264_: *mut leanh::LeanObject,
    mut v_a_5265_: *mut leanh::LeanObject,
    mut v_a_5266_: *mut leanh::LeanObject,
    mut v_a_5267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origCont_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureBase_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_liftedDoBlockResultType_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5284_: u8 = 0;
    let mut v_resultName_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v_monadInfo_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVars_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVarDefs_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deadCode_5293_: u8 = 0;
    let mut v_ops_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: u8 = 0;
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5306_: u8 = 0;
    let mut v_unused_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5308_: u8 = 0;
    let mut v_unused_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_returnBase_x3f_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v_unused_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_continueBase_x3f_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5338_: u8 = 0;
    let mut v_breakBase_x3f_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_continueBase_x3f_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v___y_5346_: u8 = 0;
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5353_: u8 = 0;
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut v_a_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut v_a_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5366_: u8 = 0;
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5370_: u8 = 0;
    let mut v_a_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5374_: u8 = 0;
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5269_ = l_Lean_Elab_Do_getBreakCont___redArg(v_a_5261_);
                if leanh::lean_obj_tag(v___x_5269_) == 0 {
                    v_a_5270_ = leanh::lean_ctor_get(v___x_5269_, 0);
                    leanh::lean_inc(v_a_5270_);
                    leanh::lean_dec_ref_known(v___x_5269_, 1);
                    v___x_5271_ = l_Lean_Elab_Do_getContinueCont___redArg(v_a_5261_);
                    if leanh::lean_obj_tag(v___x_5271_) == 0 {
                        v_a_5272_ = leanh::lean_ctor_get(v___x_5271_, 0);
                        leanh::lean_inc(v_a_5272_);
                        leanh::lean_dec_ref_known(v___x_5271_, 1);
                        v___x_5273_ = l_Lean_Elab_Do_getReturnCont___redArg(v_a_5261_);
                        if leanh::lean_obj_tag(v___x_5273_) == 0 {
                            v_a_5274_ = leanh::lean_ctor_get(v___x_5273_, 0);
                            leanh::lean_inc(v_a_5274_);
                            leanh::lean_dec_ref_known(v___x_5273_, 1);
                            if leanh::lean_obj_tag(v_a_5270_) == 1 {
                                v_breakBase_x3f_5339_ = leanh::lean_ctor_get(v_l_5259_, 2);
                                leanh::lean_inc(v_breakBase_x3f_5339_);
                                if leanh::lean_obj_tag(v_breakBase_x3f_5339_) == 1 {
                                    leanh::lean_dec_ref_known(v_a_5270_, 1);
                                    v_continueBase_x3f_5340_ =
                                        leanh::lean_ctor_get(v_l_5259_, 3);
                                    v_val_5341_ =
                                        leanh::lean_ctor_get(v_breakBase_x3f_5339_, 0);
                                    v_isSharedCheck_5354_ =
                                        (!leanh::lean_is_exclusive(v_breakBase_x3f_5339_))
                                            as u8;
                                    if v_isSharedCheck_5354_ == 0 {
                                        v___x_5343_ = v_breakBase_x3f_5339_;
                                        v_isShared_5344_ = v_isSharedCheck_5354_;
                                        state = 12;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_5341_);
                                        leanh::lean_dec(v_breakBase_x3f_5339_);
                                        v___x_5343_ = leanh::lean_box(0);
                                        v_isShared_5344_ = v_isSharedCheck_5354_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_breakBase_x3f_5339_);
                                    v___y_5328_ = v_a_5270_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v___y_5328_ = v_a_5270_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5272_);
                            leanh::lean_dec(v_a_5270_);
                            leanh::lean_dec_ref(v_elabElem_5260_);
                            leanh::lean_dec_ref(v_l_5259_);
                            v_a_5355_ = leanh::lean_ctor_get(v___x_5273_, 0);
                            v_isSharedCheck_5362_ =
                                (!leanh::lean_is_exclusive(v___x_5273_)) as u8;
                            if v_isSharedCheck_5362_ == 0 {
                                v___x_5357_ = v___x_5273_;
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5355_);
                                leanh::lean_dec(v___x_5273_);
                                v___x_5357_ = leanh::lean_box(0);
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5270_);
                        leanh::lean_dec_ref(v_elabElem_5260_);
                        leanh::lean_dec_ref(v_l_5259_);
                        v_a_5363_ = leanh::lean_ctor_get(v___x_5271_, 0);
                        v_isSharedCheck_5370_ =
                            (!leanh::lean_is_exclusive(v___x_5271_)) as u8;
                        if v_isSharedCheck_5370_ == 0 {
                            v___x_5365_ = v___x_5271_;
                            v_isShared_5366_ = v_isSharedCheck_5370_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5363_);
                            leanh::lean_dec(v___x_5271_);
                            v___x_5365_ = leanh::lean_box(0);
                            v_isShared_5366_ = v_isSharedCheck_5370_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_elabElem_5260_);
                    leanh::lean_dec_ref(v_l_5259_);
                    v_a_5371_ = leanh::lean_ctor_get(v___x_5269_, 0);
                    v_isSharedCheck_5378_ = (!leanh::lean_is_exclusive(v___x_5269_)) as u8;
                    if v_isSharedCheck_5378_ == 0 {
                        v___x_5373_ = v___x_5269_;
                        v_isShared_5374_ = v_isSharedCheck_5378_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5371_);
                        leanh::lean_dec(v___x_5269_);
                        v___x_5373_ = leanh::lean_box(0);
                        v_isShared_5374_ = v_isSharedCheck_5378_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v_origCont_5279_ = leanh::lean_ctor_get(v_l_5259_, 0);
                v_pureBase_5280_ = leanh::lean_ctor_get(v_l_5259_, 4);
                v_liftedDoBlockResultType_5281_ = leanh::lean_ctor_get(v_l_5259_, 5);
                v_isSharedCheck_5308_ = (!leanh::lean_is_exclusive(v_l_5259_)) as u8;
                if v_isSharedCheck_5308_ == 0 {
                    v_unused_5309_ = leanh::lean_ctor_get(v_l_5259_, 3);
                    leanh::lean_dec(v_unused_5309_);
                    v_unused_5310_ = leanh::lean_ctor_get(v_l_5259_, 2);
                    leanh::lean_dec(v_unused_5310_);
                    v_unused_5311_ = leanh::lean_ctor_get(v_l_5259_, 1);
                    leanh::lean_dec(v_unused_5311_);
                    v___x_5283_ = v_l_5259_;
                    v_isShared_5284_ = v_isSharedCheck_5308_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_liftedDoBlockResultType_5281_);
                    leanh::lean_inc(v_pureBase_5280_);
                    leanh::lean_inc(v_origCont_5279_);
                    leanh::lean_dec(v_l_5259_);
                    v___x_5283_ = leanh::lean_box(0);
                    v_isShared_5284_ = v_isSharedCheck_5308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_resultName_5285_ = leanh::lean_ctor_get(v_origCont_5279_, 0);
                v_resultType_5286_ = leanh::lean_ctor_get(v_origCont_5279_, 1);
                v_isSharedCheck_5306_ = (!leanh::lean_is_exclusive(v_origCont_5279_)) as u8;
                if v_isSharedCheck_5306_ == 0 {
                    v_unused_5307_ = leanh::lean_ctor_get(v_origCont_5279_, 2);
                    leanh::lean_dec(v_unused_5307_);
                    v___x_5288_ = v_origCont_5279_;
                    v_isShared_5289_ = v_isSharedCheck_5306_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_resultType_5286_);
                    leanh::lean_inc(v_resultName_5285_);
                    leanh::lean_dec(v_origCont_5279_);
                    v___x_5288_ = leanh::lean_box(0);
                    v_isShared_5289_ = v_isSharedCheck_5306_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_monadInfo_5290_ = leanh::lean_ctor_get(v_a_5261_, 0);
                v_mutVars_5291_ = leanh::lean_ctor_get(v_a_5261_, 1);
                v_mutVarDefs_5292_ = leanh::lean_ctor_get(v_a_5261_, 2);
                v_deadCode_5293_ = leanh::lean_ctor_get_uint8(
                    v_a_5261_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_ops_5294_ = leanh::lean_ctor_get(v_a_5261_, 5);
                leanh::lean_inc(v_resultName_5285_);
                v___x_5295_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_mkPure___boxed as *mut core::ffi::c_void,
                    10,
                    2,
                );
                leanh::lean_closure_set(v___x_5295_, 0, v_pureBase_5280_);
                leanh::lean_closure_set(v___x_5295_, 1, v_resultName_5285_);
                v___x_5296_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5296_, 0, v___y_5278_);
                leanh::lean_ctor_set(v___x_5296_, 1, v___y_5276_);
                leanh::lean_ctor_set(v___x_5296_, 2, v___y_5277_);
                v___x_5297_ = l_Lean_Elab_Do_ContInfo_toContInfoRefImpl(v___x_5296_);
                leanh::lean_dec_ref_known(v___x_5296_, 3);
                v___x_5298_ = 1;
                if v_isShared_5289_ == 0 {
                    leanh::lean_ctor_set(v___x_5288_, 2, v___x_5295_);
                    v___x_5300_ = v___x_5288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5305_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_resultName_5285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5305_, 1, v_resultType_5286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5305_, 2, v___x_5295_);
                    v___x_5300_ = v_reuseFailAlloc_5305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5300_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_5298_,
                );
                leanh::lean_inc(v_ops_5294_);
                leanh::lean_inc_ref(v_mutVarDefs_5292_);
                leanh::lean_inc_ref(v_mutVars_5291_);
                leanh::lean_inc_ref(v_monadInfo_5290_);
                if v_isShared_5284_ == 0 {
                    leanh::lean_ctor_set(v___x_5283_, 5, v_ops_5294_);
                    leanh::lean_ctor_set(v___x_5283_, 4, v___x_5297_);
                    leanh::lean_ctor_set(v___x_5283_, 3, v_liftedDoBlockResultType_5281_);
                    leanh::lean_ctor_set(v___x_5283_, 2, v_mutVarDefs_5292_);
                    leanh::lean_ctor_set(v___x_5283_, 1, v_mutVars_5291_);
                    leanh::lean_ctor_set(v___x_5283_, 0, v_monadInfo_5290_);
                    v___x_5302_ = v___x_5283_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_monadInfo_5290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 1, v_mutVars_5291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 2, v_mutVarDefs_5292_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5304_,
                        3,
                        v_liftedDoBlockResultType_5281_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 4, v___x_5297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 5, v_ops_5294_);
                    v___x_5302_ = v_reuseFailAlloc_5304_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5302_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    v_deadCode_5293_,
                );
                leanh::lean_inc(v_a_5267_);
                leanh::lean_inc_ref(v_a_5266_);
                leanh::lean_inc(v_a_5265_);
                leanh::lean_inc_ref(v_a_5264_);
                leanh::lean_inc(v_a_5263_);
                leanh::lean_inc_ref(v_a_5262_);
                v___x_5303_ = leanh::lean_apply_9(
                    v_elabElem_5260_,
                    v___x_5300_,
                    v___x_5302_,
                    v_a_5262_,
                    v_a_5263_,
                    v_a_5264_,
                    v_a_5265_,
                    v_a_5266_,
                    v_a_5267_,
                    leanh::lean_box(0),
                );
                return v___x_5303_;
            }
            6 => {
                v_returnBase_x3f_5315_ = leanh::lean_ctor_get(v_l_5259_, 1);
                if leanh::lean_obj_tag(v_returnBase_x3f_5315_) == 1 {
                    v_val_5316_ = leanh::lean_ctor_get(v_returnBase_x3f_5315_, 0);
                    v_resultType_5317_ = leanh::lean_ctor_get(v_a_5274_, 0);
                    v_isSharedCheck_5325_ = (!leanh::lean_is_exclusive(v_a_5274_)) as u8;
                    if v_isSharedCheck_5325_ == 0 {
                        v_unused_5326_ = leanh::lean_ctor_get(v_a_5274_, 1);
                        leanh::lean_dec(v_unused_5326_);
                        v___x_5319_ = v_a_5274_;
                        v_isShared_5320_ = v_isSharedCheck_5325_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_resultType_5317_);
                        leanh::lean_dec(v_a_5274_);
                        v___x_5319_ = leanh::lean_box(0);
                        v_isShared_5320_ = v_isSharedCheck_5325_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___y_5276_ = v___y_5313_;
                    v___y_5277_ = v___y_5314_;
                    v___y_5278_ = v_a_5274_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v_val_5316_);
                v___x_5321_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_mkReturn___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                leanh::lean_closure_set(v___x_5321_, 0, v_val_5316_);
                if v_isShared_5320_ == 0 {
                    leanh::lean_ctor_set(v___x_5319_, 1, v___x_5321_);
                    v___x_5323_ = v___x_5319_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_resultType_5317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5324_, 1, v___x_5321_);
                    v___x_5323_ = v_reuseFailAlloc_5324_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_5276_ = v___y_5313_;
                v___y_5277_ = v___y_5314_;
                v___y_5278_ = v___x_5323_;
                state = 1;
                continue;
            }
            9 => {
                if leanh::lean_obj_tag(v_a_5272_) == 1 {
                    v_continueBase_x3f_5329_ = leanh::lean_ctor_get(v_l_5259_, 3);
                    leanh::lean_inc(v_continueBase_x3f_5329_);
                    if leanh::lean_obj_tag(v_continueBase_x3f_5329_) == 1 {
                        leanh::lean_dec_ref_known(v_a_5272_, 1);
                        v_val_5330_ = leanh::lean_ctor_get(v_continueBase_x3f_5329_, 0);
                        v_isSharedCheck_5338_ =
                            (!leanh::lean_is_exclusive(v_continueBase_x3f_5329_)) as u8;
                        if v_isSharedCheck_5338_ == 0 {
                            v___x_5332_ = v_continueBase_x3f_5329_;
                            v_isShared_5333_ = v_isSharedCheck_5338_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_5330_);
                            leanh::lean_dec(v_continueBase_x3f_5329_);
                            v___x_5332_ = leanh::lean_box(0);
                            v_isShared_5333_ = v_isSharedCheck_5338_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_continueBase_x3f_5329_);
                        v___y_5313_ = v___y_5328_;
                        v___y_5314_ = v_a_5272_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___y_5313_ = v___y_5328_;
                    v___y_5314_ = v_a_5272_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_5334_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_mkContinue___boxed as *mut core::ffi::c_void,
                    9,
                    1,
                );
                leanh::lean_closure_set(v___x_5334_, 0, v_val_5330_);
                if v_isShared_5333_ == 0 {
                    leanh::lean_ctor_set(v___x_5332_, 0, v___x_5334_);
                    v___x_5336_ = v___x_5332_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5334_);
                    v___x_5336_ = v_reuseFailAlloc_5337_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_5313_ = v___y_5328_;
                v___y_5314_ = v___x_5336_;
                state = 6;
                continue;
            }
            12 => {
                if leanh::lean_obj_tag(v_continueBase_x3f_5340_) == 0 {
                    v___x_5352_ = 0;
                    v___y_5346_ = v___x_5352_;
                    state = 13;
                    continue;
                } else {
                    v___x_5353_ = 1;
                    v___y_5346_ = v___x_5353_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5347_ = leanh::lean_box((v___y_5346_) as usize);
                v___x_5348_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_ControlStack_mkBreak___boxed as *mut core::ffi::c_void,
                    10,
                    2,
                );
                leanh::lean_closure_set(v___x_5348_, 0, v_val_5341_);
                leanh::lean_closure_set(v___x_5348_, 1, v___x_5347_);
                if v_isShared_5344_ == 0 {
                    leanh::lean_ctor_set(v___x_5343_, 0, v___x_5348_);
                    v___x_5350_ = v___x_5343_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
                    v___x_5350_ = v_reuseFailAlloc_5351_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_5328_ = v___x_5350_;
                state = 9;
                continue;
            }
            15 => {
                if v_isShared_5358_ == 0 {
                    v___x_5360_ = v___x_5357_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5361_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
                    v___x_5360_ = v_reuseFailAlloc_5361_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5360_;
            }
            17 => {
                if v_isShared_5366_ == 0 {
                    v___x_5368_ = v___x_5365_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5369_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5363_);
                    v___x_5368_ = v_reuseFailAlloc_5369_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5368_;
            }
            19 => {
                if v_isShared_5374_ == 0 {
                    v___x_5376_ = v___x_5373_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
                    v___x_5376_ = v_reuseFailAlloc_5377_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlLifter_lift___boxed(
    mut v_l_5379_: *mut leanh::LeanObject,
    mut v_elabElem_5380_: *mut leanh::LeanObject,
    mut v_a_5381_: *mut leanh::LeanObject,
    mut v_a_5382_: *mut leanh::LeanObject,
    mut v_a_5383_: *mut leanh::LeanObject,
    mut v_a_5384_: *mut leanh::LeanObject,
    mut v_a_5385_: *mut leanh::LeanObject,
    mut v_a_5386_: *mut leanh::LeanObject,
    mut v_a_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5389_ = l_Lean_Elab_Do_ControlLifter_lift(
        v_l_5379_,
        v_elabElem_5380_,
        v_a_5381_,
        v_a_5382_,
        v_a_5383_,
        v_a_5384_,
        v_a_5385_,
        v_a_5386_,
        v_a_5387_,
    );
    leanh::lean_dec(v_a_5387_);
    leanh::lean_dec_ref(v_a_5386_);
    leanh::lean_dec(v_a_5385_);
    leanh::lean_dec_ref(v_a_5384_);
    leanh::lean_dec(v_a_5383_);
    leanh::lean_dec_ref(v_a_5382_);
    leanh::lean_dec_ref(v_a_5381_);
    return v_res_5389_;
}
pub unsafe fn l_Lean_Elab_Do_ControlLifter_restoreCont(
    mut v_l_5390_: *mut leanh::LeanObject,
    mut v_a_5391_: *mut leanh::LeanObject,
    mut v_a_5392_: *mut leanh::LeanObject,
    mut v_a_5393_: *mut leanh::LeanObject,
    mut v_a_5394_: *mut leanh::LeanObject,
    mut v_a_5395_: *mut leanh::LeanObject,
    mut v_a_5396_: *mut leanh::LeanObject,
    mut v_a_5397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pureBase_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origCont_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureDeadCode_5401_: u8 = 0;
    let mut v_restoreCont_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultName_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_5406_: u8 = 0;
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pureBase_5399_ = leanh::lean_ctor_get(v_l_5390_, 4);
                leanh::lean_inc_ref(v_pureBase_5399_);
                v_origCont_5400_ = leanh::lean_ctor_get(v_l_5390_, 0);
                leanh::lean_inc_ref(v_origCont_5400_);
                v_pureDeadCode_5401_ = leanh::lean_ctor_get_uint8(
                    v_l_5390_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                leanh::lean_dec_ref(v_l_5390_);
                v_restoreCont_5402_ = leanh::lean_ctor_get(v_pureBase_5399_, 4);
                leanh::lean_inc_ref(v_restoreCont_5402_);
                leanh::lean_dec_ref(v_pureBase_5399_);
                v_resultName_5403_ = leanh::lean_ctor_get(v_origCont_5400_, 0);
                v_resultType_5404_ = leanh::lean_ctor_get(v_origCont_5400_, 1);
                v_k_5405_ = leanh::lean_ctor_get(v_origCont_5400_, 2);
                v_kind_5406_ = leanh::lean_ctor_get_uint8(
                    v_origCont_5400_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_5416_ = (!leanh::lean_is_exclusive(v_origCont_5400_)) as u8;
                if v_isSharedCheck_5416_ == 0 {
                    v___x_5408_ = v_origCont_5400_;
                    v_isShared_5409_ = v_isSharedCheck_5416_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_k_5405_);
                    leanh::lean_inc(v_resultType_5404_);
                    leanh::lean_inc(v_resultName_5403_);
                    leanh::lean_dec(v_origCont_5400_);
                    v___x_5408_ = leanh::lean_box(0);
                    v_isShared_5409_ = v_isSharedCheck_5416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5410_ = leanh::lean_box((v_pureDeadCode_5401_) as usize);
                v___x_5411_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_withDeadCode___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                leanh::lean_closure_set(v___x_5411_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_5411_, 1, v___x_5410_);
                leanh::lean_closure_set(v___x_5411_, 2, v_k_5405_);
                if v_isShared_5409_ == 0 {
                    leanh::lean_ctor_set(v___x_5408_, 2, v___x_5411_);
                    v___x_5413_ = v___x_5408_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5415_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_resultName_5403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5415_, 1, v_resultType_5404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5415_, 2, v___x_5411_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5415_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_kind_5406_,
                    );
                    v___x_5413_ = v_reuseFailAlloc_5415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_a_5397_);
                leanh::lean_inc_ref(v_a_5396_);
                leanh::lean_inc(v_a_5395_);
                leanh::lean_inc_ref(v_a_5394_);
                leanh::lean_inc(v_a_5393_);
                leanh::lean_inc_ref(v_a_5392_);
                leanh::lean_inc_ref(v_a_5391_);
                v___x_5414_ = leanh::lean_apply_9(
                    v_restoreCont_5402_,
                    v___x_5413_,
                    v_a_5391_,
                    v_a_5392_,
                    v_a_5393_,
                    v_a_5394_,
                    v_a_5395_,
                    v_a_5396_,
                    v_a_5397_,
                    leanh::lean_box(0),
                );
                return v___x_5414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_ControlLifter_restoreCont___boxed(
    mut v_l_5417_: *mut leanh::LeanObject,
    mut v_a_5418_: *mut leanh::LeanObject,
    mut v_a_5419_: *mut leanh::LeanObject,
    mut v_a_5420_: *mut leanh::LeanObject,
    mut v_a_5421_: *mut leanh::LeanObject,
    mut v_a_5422_: *mut leanh::LeanObject,
    mut v_a_5423_: *mut leanh::LeanObject,
    mut v_a_5424_: *mut leanh::LeanObject,
    mut v_a_5425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5426_ = l_Lean_Elab_Do_ControlLifter_restoreCont(
        v_l_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_,
    );
    leanh::lean_dec(v_a_5424_);
    leanh::lean_dec_ref(v_a_5423_);
    leanh::lean_dec(v_a_5422_);
    leanh::lean_dec_ref(v_a_5421_);
    leanh::lean_dec(v_a_5420_);
    leanh::lean_dec_ref(v_a_5419_);
    leanh::lean_dec_ref(v_a_5418_);
    return v_res_5426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Do_Control(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_ProdN(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Do_Control(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Do_Control(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_ProdN(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Do_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Do_Control(builtin);
}