// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Entails
// Imports: Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.Util Lean.Meta.Sym.Util
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr4;
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Context::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Reduce::l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead;
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Util::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util,
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_forallE___override, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    l_Lean_Meta_Sym_Internal_Sym_assertShared, l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::l_Lean_Meta_Sym_isDefEqS;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommonInc___redArg;
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_unfoldReducible,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::l_Lean_MVarId_replaceTargetDefEq;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
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
        69, 120, 112, 101, 99, 116, 101, 100, 32, 83, 80, 114, 101, 100, 46, 101, 110, 116, 97,
        105, 108, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value:
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value:
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
    m_data: [101, 110, 116, 97, 105, 108, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        515334035361346902 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [65, 112, 112, 108, 121, 105, 110, 103, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value:
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
    m_data: [84, 114, 105, 112, 108, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        111, 102, 95, 101, 110, 116, 97, 105, 108, 115, 95, 119, 112, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        11963640885769744415 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        5695465360175800255 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7_value:
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
    m_data: [32, 116, 111, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10_value:
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
    m_data: [32, 102, 97, 105, 108, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [69, 120, 99, 101, 112, 116, 67, 111, 110, 100, 115, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,17808102113152393460 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,7198879216713715016 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        78, 111, 116, 32, 97, 32, 83, 80, 114, 101, 100, 46, 101, 110, 116, 97, 105, 108, 115, 58,
        32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        78, 111, 116, 32, 97, 32, 102, 111, 114, 97, 108, 108, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value:
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
    m_data: [80, 111, 115, 116, 67, 111, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,3393990892394863740 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,717208579114757920 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5_value:
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
        32, 102, 97, 105, 108, 101, 100, 46, 32, 73, 116, 32, 115, 104, 111, 117, 108, 100, 32,
        110, 111, 116, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        97, 102, 116, 101, 114, 32, 97, 112, 112, 108, 121, 105, 110, 103, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        101, 110, 116, 97, 105, 108, 115, 95, 99, 111, 110, 115, 95, 105, 110, 116, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        16895493190937329785 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 32, 115, 116, 97, 116, 101, 32, 97, 116, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [32, 100, 101, 115, 112, 105, 116, 101, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 115, 112, 101, 99, 32, 112, 111, 116, 101, 110, 116, 105, 97, 108, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [112, 117, 114, 101, 95, 101, 108, 105, 109, 39, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        16366591063295091858 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value:
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
    m_data: [112, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        7100147834070349651 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value:
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
        101, 110, 116, 97, 105, 108, 115, 95, 110, 105, 108, 95, 105, 110, 116, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        15111254451868281553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value:
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
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
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
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [112, 117, 114, 101, 95, 105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__13_value) as *mut crate::leanh::LeanObject,16216700489815045332 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        11870096045526947150 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0(
    mut v_x_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2139_);
    crate::leanh::lean_inc_ref(v___y_2138_);
    crate::leanh::lean_inc(v___y_2137_);
    crate::leanh::lean_inc_ref(v___y_2136_);
    crate::leanh::lean_inc(v___y_2135_);
    crate::leanh::lean_inc(v___y_2134_);
    crate::leanh::lean_inc_ref(v___y_2133_);
    v___x_2145_ = crate::leanh::lean_apply_12(
        v_x_2132_,
        v___y_2133_,
        v___y_2134_,
        v___y_2135_,
        v___y_2136_,
        v___y_2137_,
        v___y_2138_,
        v___y_2139_,
        v___y_2140_,
        v___y_2141_,
        v___y_2142_,
        v___y_2143_,
        crate::leanh::lean_box(0),
    );
    return v___x_2145_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0___boxed(
    mut v_x_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0(v_x_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    crate::leanh::lean_dec(v___y_2153_);
    crate::leanh::lean_dec_ref(v___y_2152_);
    crate::leanh::lean_dec(v___y_2151_);
    crate::leanh::lean_dec_ref(v___y_2150_);
    crate::leanh::lean_dec(v___y_2149_);
    crate::leanh::lean_dec(v___y_2148_);
    crate::leanh::lean_dec_ref(v___y_2147_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(
    mut v_mvarId_2160_: *mut crate::leanh::LeanObject,
    mut v_x_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
    mut v___y_2165_: *mut crate::leanh::LeanObject,
    mut v___y_2166_: *mut crate::leanh::LeanObject,
    mut v___y_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2168_);
                crate::leanh::lean_inc_ref(v___y_2167_);
                crate::leanh::lean_inc(v___y_2166_);
                crate::leanh::lean_inc_ref(v___y_2165_);
                crate::leanh::lean_inc(v___y_2164_);
                crate::leanh::lean_inc(v___y_2163_);
                crate::leanh::lean_inc_ref(v___y_2162_);
                v___f_2174_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___f_2174_, 0, v_x_2161_);
                crate::leanh::lean_closure_set(v___f_2174_, 1, v___y_2162_);
                crate::leanh::lean_closure_set(v___f_2174_, 2, v___y_2163_);
                crate::leanh::lean_closure_set(v___f_2174_, 3, v___y_2164_);
                crate::leanh::lean_closure_set(v___f_2174_, 4, v___y_2165_);
                crate::leanh::lean_closure_set(v___f_2174_, 5, v___y_2166_);
                crate::leanh::lean_closure_set(v___f_2174_, 6, v___y_2167_);
                crate::leanh::lean_closure_set(v___f_2174_, 7, v___y_2168_);
                v___x_2175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2160_,
                    v___f_2174_,
                    v___y_2169_,
                    v___y_2170_,
                    v___y_2171_,
                    v___y_2172_,
                );
                if crate::leanh::lean_obj_tag(v___x_2175_) == 0 {
                    return v___x_2175_;
                } else {
                    v_a_2176_ = crate::leanh::lean_ctor_get(v___x_2175_, 0);
                    v_isSharedCheck_2183_ = (!crate::leanh::lean_is_exclusive(v___x_2175_)) as u8;
                    if v_isSharedCheck_2183_ == 0 {
                        v___x_2178_ = v___x_2175_;
                        v_isShared_2179_ = v_isSharedCheck_2183_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2176_);
                        crate::leanh::lean_dec(v___x_2175_);
                        v___x_2178_ = crate::leanh::lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2183_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2179_ == 0 {
                    v___x_2181_ = v___x_2178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
                    v___x_2181_ = v_reuseFailAlloc_2182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg___boxed(
    mut v_mvarId_2184_: *mut crate::leanh::LeanObject,
    mut v_x_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
    mut v___y_2188_: *mut crate::leanh::LeanObject,
    mut v___y_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
    mut v___y_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_mvarId_2184_, v_x_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
    crate::leanh::lean_dec(v___y_2196_);
    crate::leanh::lean_dec_ref(v___y_2195_);
    crate::leanh::lean_dec(v___y_2194_);
    crate::leanh::lean_dec_ref(v___y_2193_);
    crate::leanh::lean_dec(v___y_2192_);
    crate::leanh::lean_dec_ref(v___y_2191_);
    crate::leanh::lean_dec(v___y_2190_);
    crate::leanh::lean_dec_ref(v___y_2189_);
    crate::leanh::lean_dec(v___y_2188_);
    crate::leanh::lean_dec(v___y_2187_);
    crate::leanh::lean_dec_ref(v___y_2186_);
    return v_res_2198_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2(
    mut v_00_u03b1_2199_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2200_: *mut crate::leanh::LeanObject,
    mut v_x_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_mvarId_2200_, v_x_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
    return v___x_2214_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___boxed(
    mut v_00_u03b1_2215_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2216_: *mut crate::leanh::LeanObject,
    mut v_x_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
    mut v___y_2226_: *mut crate::leanh::LeanObject,
    mut v___y_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
    mut v___y_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2(
            v_00_u03b1_2215_,
            v_mvarId_2216_,
            v_x_2217_,
            v___y_2218_,
            v___y_2219_,
            v___y_2220_,
            v___y_2221_,
            v___y_2222_,
            v___y_2223_,
            v___y_2224_,
            v___y_2225_,
            v___y_2226_,
            v___y_2227_,
            v___y_2228_,
        );
    crate::leanh::lean_dec(v___y_2228_);
    crate::leanh::lean_dec_ref(v___y_2227_);
    crate::leanh::lean_dec(v___y_2226_);
    crate::leanh::lean_dec_ref(v___y_2225_);
    crate::leanh::lean_dec(v___y_2224_);
    crate::leanh::lean_dec_ref(v___y_2223_);
    crate::leanh::lean_dec(v___y_2222_);
    crate::leanh::lean_dec_ref(v___y_2221_);
    crate::leanh::lean_dec(v___y_2220_);
    crate::leanh::lean_dec(v___y_2219_);
    crate::leanh::lean_dec_ref(v___y_2218_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(
    mut v_msgData_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = lean_st_ref_get(v___y_2235_);
    v_env_2238_ = crate::leanh::lean_ctor_get(v___x_2237_, 0);
    crate::leanh::lean_inc_ref(v_env_2238_);
    crate::leanh::lean_dec(v___x_2237_);
    v___x_2239_ = lean_st_ref_get(v___y_2233_);
    v_mctx_2240_ = crate::leanh::lean_ctor_get(v___x_2239_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2240_);
    crate::leanh::lean_dec(v___x_2239_);
    v_lctx_2241_ = crate::leanh::lean_ctor_get(v___y_2232_, 2);
    v_options_2242_ = crate::leanh::lean_ctor_get(v___y_2234_, 2);
    crate::leanh::lean_inc_ref(v_options_2242_);
    crate::leanh::lean_inc_ref(v_lctx_2241_);
    v___x_2243_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2243_, 0, v_env_2238_);
    crate::leanh::lean_ctor_set(v___x_2243_, 1, v_mctx_2240_);
    crate::leanh::lean_ctor_set(v___x_2243_, 2, v_lctx_2241_);
    crate::leanh::lean_ctor_set(v___x_2243_, 3, v_options_2242_);
    v___x_2244_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2243_);
    crate::leanh::lean_ctor_set(v___x_2244_, 1, v_msgData_2231_);
    v___x_2245_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0___boxed(
    mut v_msgData_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(v_msgData_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
    crate::leanh::lean_dec(v___y_2250_);
    crate::leanh::lean_dec_ref(v___y_2249_);
    crate::leanh::lean_dec(v___y_2248_);
    crate::leanh::lean_dec_ref(v___y_2247_);
    return v_res_2252_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(
    mut v_msg_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2259_ = crate::leanh::lean_ctor_get(v___y_2256_, 5);
                v___x_2260_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0_spec__0(v_msg_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
                v_a_2261_ = crate::leanh::lean_ctor_get(v___x_2260_, 0);
                v_isSharedCheck_2269_ = (!crate::leanh::lean_is_exclusive(v___x_2260_)) as u8;
                if v_isSharedCheck_2269_ == 0 {
                    v___x_2263_ = v___x_2260_;
                    v_isShared_2264_ = v_isSharedCheck_2269_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2261_);
                    crate::leanh::lean_dec(v___x_2260_);
                    v___x_2263_ = crate::leanh::lean_box(0);
                    v_isShared_2264_ = v_isSharedCheck_2269_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2259_);
                v___x_2265_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2265_, 0, v_ref_2259_);
                crate::leanh::lean_ctor_set(v___x_2265_, 1, v_a_2261_);
                if v_isShared_2264_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2263_, 1);
                    crate::leanh::lean_ctor_set(v___x_2263_, 0, v___x_2265_);
                    v___x_2267_ = v___x_2263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
                    v___x_2267_ = v_reuseFailAlloc_2268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg___boxed(
    mut v_msg_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(
            v_msg_2270_,
            v___y_2271_,
            v___y_2272_,
            v___y_2273_,
            v___y_2274_,
        );
    crate::leanh::lean_dec(v___y_2274_);
    crate::leanh::lean_dec_ref(v___y_2273_);
    crate::leanh::lean_dec(v___y_2272_);
    crate::leanh::lean_dec_ref(v___y_2271_);
    return v_res_2276_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(
    mut v_f_2277_: *mut crate::leanh::LeanObject,
    mut v_a_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2291_: u8 = 0;
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2297_: u8 = 0;
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2301_: u8 = 0;
    let mut v_a_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2290_ = lean_st_ref_get(v___y_2280_);
                v_debug_2291_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2290_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_2290_);
                if v_debug_2291_ == 0 {
                    v___y_2287_ = v___y_2280_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_2277_);
                    v___x_2292_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_2277_,
                        v___y_2279_,
                        v___y_2280_,
                        v___y_2281_,
                        v___y_2282_,
                        v___y_2283_,
                        v___y_2284_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2292_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2292_, 1);
                        crate::leanh::lean_inc_ref(v_a_2278_);
                        v___x_2293_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_2278_,
                            v___y_2279_,
                            v___y_2280_,
                            v___y_2281_,
                            v___y_2282_,
                            v___y_2283_,
                            v___y_2284_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2293_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2293_, 1);
                            v___y_2287_ = v___y_2280_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_2278_);
                            crate::leanh::lean_dec_ref(v_f_2277_);
                            v_a_2294_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                            v_isSharedCheck_2301_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2293_)) as u8;
                            if v_isSharedCheck_2301_ == 0 {
                                v___x_2296_ = v___x_2293_;
                                v_isShared_2297_ = v_isSharedCheck_2301_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2294_);
                                crate::leanh::lean_dec(v___x_2293_);
                                v___x_2296_ = crate::leanh::lean_box(0);
                                v_isShared_2297_ = v_isSharedCheck_2301_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2278_);
                        crate::leanh::lean_dec_ref(v_f_2277_);
                        v_a_2302_ = crate::leanh::lean_ctor_get(v___x_2292_, 0);
                        v_isSharedCheck_2309_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2292_)) as u8;
                        if v_isSharedCheck_2309_ == 0 {
                            v___x_2304_ = v___x_2292_;
                            v_isShared_2305_ = v_isSharedCheck_2309_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2302_);
                            crate::leanh::lean_dec(v___x_2292_);
                            v___x_2304_ = crate::leanh::lean_box(0);
                            v_isShared_2305_ = v_isSharedCheck_2309_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2288_ = l_Lean_Expr_app___override(v_f_2277_, v_a_2278_);
                v___x_2289_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2288_, v___y_2287_);
                return v___x_2289_;
            }
            2 => {
                if v_isShared_2297_ == 0 {
                    v___x_2299_ = v___x_2296_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
                    v___x_2299_ = v_reuseFailAlloc_2300_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2299_;
            }
            4 => {
                if v_isShared_2305_ == 0 {
                    v___x_2307_ = v___x_2304_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
                    v___x_2307_ = v_reuseFailAlloc_2308_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg___boxed(
    mut v_f_2310_: *mut crate::leanh::LeanObject,
    mut v_a_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2319_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_2310_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
    crate::leanh::lean_dec(v___y_2317_);
    crate::leanh::lean_dec_ref(v___y_2316_);
    crate::leanh::lean_dec(v___y_2315_);
    crate::leanh::lean_dec_ref(v___y_2314_);
    crate::leanh::lean_dec(v___y_2313_);
    crate::leanh::lean_dec_ref(v___y_2312_);
    return v_res_2319_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(
    mut v_f_2320_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_2321_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_2320_, v_a_u2081_2321_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
    if crate::leanh::lean_obj_tag(v___x_2335_) == 0 {
        let mut v_a_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2336_ = crate::leanh::lean_ctor_get(v___x_2335_, 0);
        crate::leanh::lean_inc(v_a_2336_);
        crate::leanh::lean_dec_ref_known(v___x_2335_, 1);
        v___x_2337_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_a_2336_, v_a_u2082_2322_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
        return v___x_2337_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2082_2322_);
        return v___x_2335_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2___boxed(
    mut v_f_2338_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_2339_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
    mut v___y_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(v_f_2338_, v_a_u2081_2339_, v_a_u2082_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
    crate::leanh::lean_dec(v___y_2351_);
    crate::leanh::lean_dec_ref(v___y_2350_);
    crate::leanh::lean_dec(v___y_2349_);
    crate::leanh::lean_dec_ref(v___y_2348_);
    crate::leanh::lean_dec(v___y_2347_);
    crate::leanh::lean_dec_ref(v___y_2346_);
    crate::leanh::lean_dec(v___y_2345_);
    crate::leanh::lean_dec_ref(v___y_2344_);
    crate::leanh::lean_dec(v___y_2343_);
    crate::leanh::lean_dec(v___y_2342_);
    crate::leanh::lean_dec_ref(v___y_2341_);
    return v_res_2353_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(
    mut v_f_2354_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_2355_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_2356_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2370_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__2(v_f_2354_, v_a_u2081_2355_, v_a_u2082_2356_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
    if crate::leanh::lean_obj_tag(v___x_2370_) == 0 {
        let mut v_a_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2371_ = crate::leanh::lean_ctor_get(v___x_2370_, 0);
        crate::leanh::lean_inc(v_a_2371_);
        crate::leanh::lean_dec_ref_known(v___x_2370_, 1);
        v___x_2372_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_a_2371_, v_a_u2083_2357_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
        return v___x_2372_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2083_2357_);
        return v___x_2370_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1___boxed(
    mut v_f_2373_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_2374_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_2375_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v_f_2373_, v_a_u2081_2374_, v_a_u2082_2375_, v_a_u2083_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
    crate::leanh::lean_dec(v___y_2387_);
    crate::leanh::lean_dec_ref(v___y_2386_);
    crate::leanh::lean_dec(v___y_2385_);
    crate::leanh::lean_dec_ref(v___y_2384_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v___y_2382_);
    crate::leanh::lean_dec(v___y_2381_);
    crate::leanh::lean_dec_ref(v___y_2380_);
    crate::leanh::lean_dec(v___y_2379_);
    crate::leanh::lean_dec(v___y_2378_);
    crate::leanh::lean_dec_ref(v___y_2377_);
    return v_res_2389_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__0;
    v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0(
    mut v_head_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: u8 = 0;
    let mut v_arg_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v_arg_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: u8 = 0;
    let mut v_arg_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_a_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut v_a_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2475_: u8 = 0;
    let mut v_a_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_head_2402_);
                v___x_2415_ = l_Lean_MVarId_getType(
                    v_head_2402_,
                    v___y_2410_,
                    v___y_2411_,
                    v___y_2412_,
                    v___y_2413_,
                );
                if crate::leanh::lean_obj_tag(v___x_2415_) == 0 {
                    v_a_2416_ = crate::leanh::lean_ctor_get(v___x_2415_, 0);
                    crate::leanh::lean_inc_n(v_a_2416_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2415_, 1);
                    v___x_2433_ = l_Lean_Expr_cleanupAnnotations(v_a_2416_);
                    v___x_2434_ = l_Lean_Expr_isApp(v___x_2433_);
                    if v___x_2434_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2433_);
                        crate::leanh::lean_dec(v_head_2402_);
                        v___y_2418_ = v___y_2403_;
                        v___y_2419_ = v___y_2404_;
                        v___y_2420_ = v___y_2405_;
                        v___y_2421_ = v___y_2406_;
                        v___y_2422_ = v___y_2407_;
                        v___y_2423_ = v___y_2408_;
                        v___y_2424_ = v___y_2409_;
                        v___y_2425_ = v___y_2410_;
                        v___y_2426_ = v___y_2411_;
                        v___y_2427_ = v___y_2412_;
                        v___y_2428_ = v___y_2413_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_2435_ = crate::leanh::lean_ctor_get(v___x_2433_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2435_);
                        v___x_2436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2433_);
                        v___x_2437_ = l_Lean_Expr_isApp(v___x_2436_);
                        if v___x_2437_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2436_);
                            crate::leanh::lean_dec_ref(v_arg_2435_);
                            crate::leanh::lean_dec(v_head_2402_);
                            v___y_2418_ = v___y_2403_;
                            v___y_2419_ = v___y_2404_;
                            v___y_2420_ = v___y_2405_;
                            v___y_2421_ = v___y_2406_;
                            v___y_2422_ = v___y_2407_;
                            v___y_2423_ = v___y_2408_;
                            v___y_2424_ = v___y_2409_;
                            v___y_2425_ = v___y_2410_;
                            v___y_2426_ = v___y_2411_;
                            v___y_2427_ = v___y_2412_;
                            v___y_2428_ = v___y_2413_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_2438_ = crate::leanh::lean_ctor_get(v___x_2436_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2438_);
                            v___x_2439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2436_);
                            v___x_2440_ = l_Lean_Expr_isApp(v___x_2439_);
                            if v___x_2440_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2439_);
                                crate::leanh::lean_dec_ref(v_arg_2438_);
                                crate::leanh::lean_dec_ref(v_arg_2435_);
                                crate::leanh::lean_dec(v_head_2402_);
                                v___y_2418_ = v___y_2403_;
                                v___y_2419_ = v___y_2404_;
                                v___y_2420_ = v___y_2405_;
                                v___y_2421_ = v___y_2406_;
                                v___y_2422_ = v___y_2407_;
                                v___y_2423_ = v___y_2408_;
                                v___y_2424_ = v___y_2409_;
                                v___y_2425_ = v___y_2410_;
                                v___y_2426_ = v___y_2411_;
                                v___y_2427_ = v___y_2412_;
                                v___y_2428_ = v___y_2413_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_2441_ = crate::leanh::lean_ctor_get(v___x_2439_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2441_);
                                v___x_2442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2439_);
                                v___x_2443_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6;
                                v___x_2444_ = l_Lean_Expr_isConstOf(v___x_2442_, v___x_2443_);
                                if v___x_2444_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2442_);
                                    crate::leanh::lean_dec_ref(v_arg_2441_);
                                    crate::leanh::lean_dec_ref(v_arg_2438_);
                                    crate::leanh::lean_dec_ref(v_arg_2435_);
                                    crate::leanh::lean_dec(v_head_2402_);
                                    v___y_2418_ = v___y_2403_;
                                    v___y_2419_ = v___y_2404_;
                                    v___y_2420_ = v___y_2405_;
                                    v___y_2421_ = v___y_2406_;
                                    v___y_2422_ = v___y_2407_;
                                    v___y_2423_ = v___y_2408_;
                                    v___y_2424_ = v___y_2409_;
                                    v___y_2425_ = v___y_2410_;
                                    v___y_2426_ = v___y_2411_;
                                    v___y_2427_ = v___y_2412_;
                                    v___y_2428_ = v___y_2413_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_2416_);
                                    v___x_2445_ = l_Lean_Meta_Sym_unfoldReducible(
                                        v_arg_2441_,
                                        v___y_2410_,
                                        v___y_2411_,
                                        v___y_2412_,
                                        v___y_2413_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2445_) == 0 {
                                        v_a_2446_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                                        crate::leanh::lean_inc(v_a_2446_);
                                        crate::leanh::lean_dec_ref_known(v___x_2445_, 1);
                                        v___x_2447_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                            v_a_2446_,
                                            v___y_2409_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2447_) == 0 {
                                            v_a_2448_ = crate::leanh::lean_ctor_get(v___x_2447_, 0);
                                            crate::leanh::lean_inc(v_a_2448_);
                                            crate::leanh::lean_dec_ref_known(v___x_2447_, 1);
                                            v___x_2449_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_2442_, v_a_2448_, v_arg_2438_, v_arg_2435_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
                                            if crate::leanh::lean_obj_tag(v___x_2449_) == 0 {
                                                v_a_2450_ =
                                                    crate::leanh::lean_ctor_get(v___x_2449_, 0);
                                                crate::leanh::lean_inc(v_a_2450_);
                                                crate::leanh::lean_dec_ref_known(v___x_2449_, 1);
                                                v___x_2451_ = l_Lean_MVarId_replaceTargetDefEq(
                                                    v_head_2402_,
                                                    v_a_2450_,
                                                    v___y_2410_,
                                                    v___y_2411_,
                                                    v___y_2412_,
                                                    v___y_2413_,
                                                );
                                                return v___x_2451_;
                                            } else {
                                                crate::leanh::lean_dec(v_head_2402_);
                                                v_a_2452_ =
                                                    crate::leanh::lean_ctor_get(v___x_2449_, 0);
                                                v_isSharedCheck_2459_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2449_))
                                                        as u8;
                                                if v_isSharedCheck_2459_ == 0 {
                                                    v___x_2454_ = v___x_2449_;
                                                    v_isShared_2455_ = v_isSharedCheck_2459_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2452_);
                                                    crate::leanh::lean_dec(v___x_2449_);
                                                    v___x_2454_ = crate::leanh::lean_box(0);
                                                    v_isShared_2455_ = v_isSharedCheck_2459_;
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2442_);
                                            crate::leanh::lean_dec_ref(v_arg_2438_);
                                            crate::leanh::lean_dec_ref(v_arg_2435_);
                                            crate::leanh::lean_dec(v_head_2402_);
                                            v_a_2460_ = crate::leanh::lean_ctor_get(v___x_2447_, 0);
                                            v_isSharedCheck_2467_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2447_))
                                                    as u8;
                                            if v_isSharedCheck_2467_ == 0 {
                                                v___x_2462_ = v___x_2447_;
                                                v_isShared_2463_ = v_isSharedCheck_2467_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2460_);
                                                crate::leanh::lean_dec(v___x_2447_);
                                                v___x_2462_ = crate::leanh::lean_box(0);
                                                v_isShared_2463_ = v_isSharedCheck_2467_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_2442_);
                                        crate::leanh::lean_dec_ref(v_arg_2438_);
                                        crate::leanh::lean_dec_ref(v_arg_2435_);
                                        crate::leanh::lean_dec(v_head_2402_);
                                        v_a_2468_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                                        v_isSharedCheck_2475_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2445_)) as u8;
                                        if v_isSharedCheck_2475_ == 0 {
                                            v___x_2470_ = v___x_2445_;
                                            v_isShared_2471_ = v_isSharedCheck_2475_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2468_);
                                            crate::leanh::lean_dec(v___x_2445_);
                                            v___x_2470_ = crate::leanh::lean_box(0);
                                            v_isShared_2471_ = v_isSharedCheck_2475_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_head_2402_);
                    v_a_2476_ = crate::leanh::lean_ctor_get(v___x_2415_, 0);
                    v_isSharedCheck_2483_ = (!crate::leanh::lean_is_exclusive(v___x_2415_)) as u8;
                    if v_isSharedCheck_2483_ == 0 {
                        v___x_2478_ = v___x_2415_;
                        v_isShared_2479_ = v_isSharedCheck_2483_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2476_);
                        crate::leanh::lean_dec(v___x_2415_);
                        v___x_2478_ = crate::leanh::lean_box(0);
                        v_isShared_2479_ = v_isSharedCheck_2483_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2429_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__1,
                );
                v___x_2430_ = l_Lean_MessageData_ofExpr(v_a_2416_);
                v___x_2431_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2431_, 0, v___x_2429_);
                crate::leanh::lean_ctor_set(v___x_2431_, 1, v___x_2430_);
                v___x_2432_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_2431_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
                return v___x_2432_;
            }
            2 => {
                if v_isShared_2455_ == 0 {
                    v___x_2457_ = v___x_2454_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2457_;
            }
            4 => {
                if v_isShared_2463_ == 0 {
                    v___x_2465_ = v___x_2462_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2466_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2465_;
            }
            6 => {
                if v_isShared_2471_ == 0 {
                    v___x_2473_ = v___x_2470_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
                    v___x_2473_ = v_reuseFailAlloc_2474_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2473_;
            }
            8 => {
                if v_isShared_2479_ == 0 {
                    v___x_2481_ = v___x_2478_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
                    v___x_2481_ = v_reuseFailAlloc_2482_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___boxed(
    mut v_head_2484_: *mut crate::leanh::LeanObject,
    mut v___y_2485_: *mut crate::leanh::LeanObject,
    mut v___y_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
    mut v___y_2489_: *mut crate::leanh::LeanObject,
    mut v___y_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
    mut v___y_2495_: *mut crate::leanh::LeanObject,
    mut v___y_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2497_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0(
        v_head_2484_,
        v___y_2485_,
        v___y_2486_,
        v___y_2487_,
        v___y_2488_,
        v___y_2489_,
        v___y_2490_,
        v___y_2491_,
        v___y_2492_,
        v___y_2493_,
        v___y_2494_,
        v___y_2495_,
    );
    crate::leanh::lean_dec(v___y_2495_);
    crate::leanh::lean_dec_ref(v___y_2494_);
    crate::leanh::lean_dec(v___y_2493_);
    crate::leanh::lean_dec_ref(v___y_2492_);
    crate::leanh::lean_dec(v___y_2491_);
    crate::leanh::lean_dec_ref(v___y_2490_);
    crate::leanh::lean_dec(v___y_2489_);
    crate::leanh::lean_dec_ref(v___y_2488_);
    crate::leanh::lean_dec(v___y_2487_);
    crate::leanh::lean_dec(v___y_2486_);
    crate::leanh::lean_dec_ref(v___y_2485_);
    return v_res_2497_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__0;
    v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
    return v___x_2500_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2508_: u8 = 0;
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = 0;
    v___x_2509_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__4;
    v___x_2510_ = l_Lean_MessageData_ofConstName(v___x_2509_, v___x_2508_);
    return v___x_2510_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2511_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__5,
    );
    v___x_2512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1,
    );
    v___x_2513_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2513_, 0, v___x_2512_);
    crate::leanh::lean_ctor_set(v___x_2513_, 1, v___x_2511_);
    return v___x_2513_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__7;
    v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
    return v___x_2516_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2517_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_2518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__6,
    );
    v___x_2519_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2518_);
    crate::leanh::lean_ctor_set(v___x_2519_, 1, v___x_2517_);
    return v___x_2519_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__10;
    v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
    return v___x_2522_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1(
    mut v_goal_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
    mut v___y_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tripleOfEntailsWPRule_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tripleOfEntailsWPRule_2536_ = crate::leanh::lean_ctor_get(v___y_2524_, 14);
                v___x_2537_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_goal_2523_);
                crate::leanh::lean_inc_ref(v_tripleOfEntailsWPRule_2536_);
                v___x_2538_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_tripleOfEntailsWPRule_2536_,
                        v_goal_2523_,
                        v___x_2537_,
                        v___y_2524_,
                        v___y_2525_,
                        v___y_2526_,
                        v___y_2527_,
                        v___y_2528_,
                        v___y_2529_,
                        v___y_2530_,
                        v___y_2531_,
                        v___y_2532_,
                        v___y_2533_,
                        v___y_2534_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2538_) == 0 {
                    v_a_2539_ = crate::leanh::lean_ctor_get(v___x_2538_, 0);
                    crate::leanh::lean_inc(v_a_2539_);
                    crate::leanh::lean_dec_ref_known(v___x_2538_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2539_) == 1 {
                        v_mvarIds_2558_ = crate::leanh::lean_ctor_get(v_a_2539_, 0);
                        crate::leanh::lean_inc(v_mvarIds_2558_);
                        crate::leanh::lean_dec_ref_known(v_a_2539_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_2558_) == 1 {
                            v_tail_2559_ = crate::leanh::lean_ctor_get(v_mvarIds_2558_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_2559_) == 0 {
                                crate::leanh::lean_dec(v_goal_2523_);
                                v_head_2560_ = crate::leanh::lean_ctor_get(v_mvarIds_2558_, 0);
                                crate::leanh::lean_inc_n(v_head_2560_, 2);
                                crate::leanh::lean_dec_ref_known(v_mvarIds_2558_, 2);
                                v___f_2561_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    13,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___f_2561_, 0, v_head_2560_);
                                v___x_2562_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_2560_, v___f_2561_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
                                return v___x_2562_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_mvarIds_2558_, 2);
                                v___y_2541_ = v___y_2524_;
                                v___y_2542_ = v___y_2525_;
                                v___y_2543_ = v___y_2526_;
                                v___y_2544_ = v___y_2527_;
                                v___y_2545_ = v___y_2528_;
                                v___y_2546_ = v___y_2529_;
                                v___y_2547_ = v___y_2530_;
                                v___y_2548_ = v___y_2531_;
                                v___y_2549_ = v___y_2532_;
                                v___y_2550_ = v___y_2533_;
                                v___y_2551_ = v___y_2534_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_2558_);
                            v___y_2541_ = v___y_2524_;
                            v___y_2542_ = v___y_2525_;
                            v___y_2543_ = v___y_2526_;
                            v___y_2544_ = v___y_2527_;
                            v___y_2545_ = v___y_2528_;
                            v___y_2546_ = v___y_2529_;
                            v___y_2547_ = v___y_2530_;
                            v___y_2548_ = v___y_2531_;
                            v___y_2549_ = v___y_2532_;
                            v___y_2550_ = v___y_2533_;
                            v___y_2551_ = v___y_2534_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2539_);
                        v___y_2541_ = v___y_2524_;
                        v___y_2542_ = v___y_2525_;
                        v___y_2543_ = v___y_2526_;
                        v___y_2544_ = v___y_2527_;
                        v___y_2545_ = v___y_2528_;
                        v___y_2546_ = v___y_2529_;
                        v___y_2547_ = v___y_2530_;
                        v___y_2548_ = v___y_2531_;
                        v___y_2549_ = v___y_2532_;
                        v___y_2550_ = v___y_2533_;
                        v___y_2551_ = v___y_2534_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_2523_);
                    v_a_2563_ = crate::leanh::lean_ctor_get(v___x_2538_, 0);
                    v_isSharedCheck_2570_ = (!crate::leanh::lean_is_exclusive(v___x_2538_)) as u8;
                    if v_isSharedCheck_2570_ == 0 {
                        v___x_2565_ = v___x_2538_;
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2563_);
                        crate::leanh::lean_dec(v___x_2538_);
                        v___x_2565_ = crate::leanh::lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2570_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2552_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__9,
                );
                v___x_2553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2553_, 0, v_goal_2523_);
                v___x_2554_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2554_, 0, v___x_2552_);
                crate::leanh::lean_ctor_set(v___x_2554_, 1, v___x_2553_);
                v___x_2555_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__11,
                );
                v___x_2556_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2556_, 0, v___x_2554_);
                crate::leanh::lean_ctor_set(v___x_2556_, 1, v___x_2555_);
                v___x_2557_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_2556_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
                return v___x_2557_;
            }
            2 => {
                if v_isShared_2566_ == 0 {
                    v___x_2568_ = v___x_2565_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___boxed(
    mut v_goal_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
    mut v___y_2580_: *mut crate::leanh::LeanObject,
    mut v___y_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1(
        v_goal_2571_,
        v___y_2572_,
        v___y_2573_,
        v___y_2574_,
        v___y_2575_,
        v___y_2576_,
        v___y_2577_,
        v___y_2578_,
        v___y_2579_,
        v___y_2580_,
        v___y_2581_,
        v___y_2582_,
    );
    crate::leanh::lean_dec(v___y_2582_);
    crate::leanh::lean_dec_ref(v___y_2581_);
    crate::leanh::lean_dec(v___y_2580_);
    crate::leanh::lean_dec_ref(v___y_2579_);
    crate::leanh::lean_dec(v___y_2578_);
    crate::leanh::lean_dec_ref(v___y_2577_);
    crate::leanh::lean_dec(v___y_2576_);
    crate::leanh::lean_dec_ref(v___y_2575_);
    crate::leanh::lean_dec(v___y_2574_);
    crate::leanh::lean_dec(v___y_2573_);
    crate::leanh::lean_dec_ref(v___y_2572_);
    return v_res_2584_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(
    mut v_goal_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
    mut v_a_2587_: *mut crate::leanh::LeanObject,
    mut v_a_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
    mut v_a_2590_: *mut crate::leanh::LeanObject,
    mut v_a_2591_: *mut crate::leanh::LeanObject,
    mut v_a_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_a_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_goal_2585_);
    v___f_2598_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___boxed as *mut core::ffi::c_void,
        13,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2598_, 0, v_goal_2585_);
    v___x_2599_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_2585_, v___f_2598_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_);
    return v___x_2599_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___boxed(
    mut v_goal_2600_: *mut crate::leanh::LeanObject,
    mut v_a_2601_: *mut crate::leanh::LeanObject,
    mut v_a_2602_: *mut crate::leanh::LeanObject,
    mut v_a_2603_: *mut crate::leanh::LeanObject,
    mut v_a_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2613_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP(
        v_goal_2600_,
        v_a_2601_,
        v_a_2602_,
        v_a_2603_,
        v_a_2604_,
        v_a_2605_,
        v_a_2606_,
        v_a_2607_,
        v_a_2608_,
        v_a_2609_,
        v_a_2610_,
        v_a_2611_,
    );
    crate::leanh::lean_dec(v_a_2611_);
    crate::leanh::lean_dec_ref(v_a_2610_);
    crate::leanh::lean_dec(v_a_2609_);
    crate::leanh::lean_dec_ref(v_a_2608_);
    crate::leanh::lean_dec(v_a_2607_);
    crate::leanh::lean_dec_ref(v_a_2606_);
    crate::leanh::lean_dec(v_a_2605_);
    crate::leanh::lean_dec_ref(v_a_2604_);
    crate::leanh::lean_dec(v_a_2603_);
    crate::leanh::lean_dec(v_a_2602_);
    crate::leanh::lean_dec_ref(v_a_2601_);
    return v_res_2613_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0(
    mut v_00_u03b1_2614_: *mut crate::leanh::LeanObject,
    mut v_msg_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
    mut v___y_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
    mut v___y_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2628_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(
            v_msg_2615_,
            v___y_2623_,
            v___y_2624_,
            v___y_2625_,
            v___y_2626_,
        );
    return v___x_2628_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___boxed(
    mut v_00_u03b1_2629_: *mut crate::leanh::LeanObject,
    mut v_msg_2630_: *mut crate::leanh::LeanObject,
    mut v___y_2631_: *mut crate::leanh::LeanObject,
    mut v___y_2632_: *mut crate::leanh::LeanObject,
    mut v___y_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
    mut v___y_2639_: *mut crate::leanh::LeanObject,
    mut v___y_2640_: *mut crate::leanh::LeanObject,
    mut v___y_2641_: *mut crate::leanh::LeanObject,
    mut v___y_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2643_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0(
        v_00_u03b1_2629_,
        v_msg_2630_,
        v___y_2631_,
        v___y_2632_,
        v___y_2633_,
        v___y_2634_,
        v___y_2635_,
        v___y_2636_,
        v___y_2637_,
        v___y_2638_,
        v___y_2639_,
        v___y_2640_,
        v___y_2641_,
    );
    crate::leanh::lean_dec(v___y_2641_);
    crate::leanh::lean_dec_ref(v___y_2640_);
    crate::leanh::lean_dec(v___y_2639_);
    crate::leanh::lean_dec_ref(v___y_2638_);
    crate::leanh::lean_dec(v___y_2637_);
    crate::leanh::lean_dec_ref(v___y_2636_);
    crate::leanh::lean_dec(v___y_2635_);
    crate::leanh::lean_dec_ref(v___y_2634_);
    crate::leanh::lean_dec(v___y_2633_);
    crate::leanh::lean_dec(v___y_2632_);
    crate::leanh::lean_dec_ref(v___y_2631_);
    return v_res_2643_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3(
    mut v_f_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
    mut v___y_2648_: *mut crate::leanh::LeanObject,
    mut v___y_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
    mut v___y_2651_: *mut crate::leanh::LeanObject,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
    mut v___y_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___redArg(v_f_2644_, v_a_2645_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3___boxed(
    mut v_f_2659_: *mut crate::leanh::LeanObject,
    mut v_a_2660_: *mut crate::leanh::LeanObject,
    mut v___y_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
    mut v___y_2665_: *mut crate::leanh::LeanObject,
    mut v___y_2666_: *mut crate::leanh::LeanObject,
    mut v___y_2667_: *mut crate::leanh::LeanObject,
    mut v___y_2668_: *mut crate::leanh::LeanObject,
    mut v___y_2669_: *mut crate::leanh::LeanObject,
    mut v___y_2670_: *mut crate::leanh::LeanObject,
    mut v___y_2671_: *mut crate::leanh::LeanObject,
    mut v___y_2672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1_spec__3(v_f_2659_, v_a_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
    crate::leanh::lean_dec(v___y_2671_);
    crate::leanh::lean_dec_ref(v___y_2670_);
    crate::leanh::lean_dec(v___y_2669_);
    crate::leanh::lean_dec_ref(v___y_2668_);
    crate::leanh::lean_dec(v___y_2667_);
    crate::leanh::lean_dec_ref(v___y_2666_);
    crate::leanh::lean_dec(v___y_2665_);
    crate::leanh::lean_dec_ref(v___y_2664_);
    crate::leanh::lean_dec(v___y_2663_);
    crate::leanh::lean_dec(v___y_2662_);
    crate::leanh::lean_dec_ref(v___y_2661_);
    return v_res_2673_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0(
    mut v_00___2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
    mut v___y_2678_: *mut crate::leanh::LeanObject,
    mut v___y_2679_: *mut crate::leanh::LeanObject,
    mut v___y_2680_: *mut crate::leanh::LeanObject,
    mut v___y_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = crate::leanh::lean_box(0);
    v___x_2688_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2688_, 0, v___x_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0___boxed(
    mut v_00___2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2702_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__0(
        v_00___2689_,
        v___y_2690_,
        v___y_2691_,
        v___y_2692_,
        v___y_2693_,
        v___y_2694_,
        v___y_2695_,
        v___y_2696_,
        v___y_2697_,
        v___y_2698_,
        v___y_2699_,
        v___y_2700_,
    );
    crate::leanh::lean_dec(v___y_2700_);
    crate::leanh::lean_dec_ref(v___y_2699_);
    crate::leanh::lean_dec(v___y_2698_);
    crate::leanh::lean_dec_ref(v___y_2697_);
    crate::leanh::lean_dec(v___y_2696_);
    crate::leanh::lean_dec_ref(v___y_2695_);
    crate::leanh::lean_dec(v___y_2694_);
    crate::leanh::lean_dec_ref(v___y_2693_);
    crate::leanh::lean_dec(v___y_2692_);
    crate::leanh::lean_dec(v___y_2691_);
    crate::leanh::lean_dec_ref(v___y_2690_);
    return v_res_2702_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1(
    mut v_goal_2709_: *mut crate::leanh::LeanObject,
    mut v___f_2710_: *mut crate::leanh::LeanObject,
    mut v___y_2711_: *mut crate::leanh::LeanObject,
    mut v___y_2712_: *mut crate::leanh::LeanObject,
    mut v___y_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    let mut v_arg_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: u8 = 0;
    let mut v_arg_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v_arg_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: u8 = 0;
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2761_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_exceptCondsEntailsPureRule_2762_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_exceptCondsEntailsFalseRule_2763_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_exceptCondsEntailsTrueRule_2764_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2768_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___y_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v___y_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2794_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_exceptCondsEntailsTrueRule_2795_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___y_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exceptCondsEntailsRflRule_2823_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_exceptCondsEntailsFalseRule_2824_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_exceptCondsEntailsTrueRule_2825_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___y_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_mvarIds_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_a_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_a_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut v_a_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2888_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut v_isSharedCheck_2893_: u8 = 0;
    let mut v_a_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_2709_);
                v___x_2723_ = l_Lean_MVarId_getType(
                    v_goal_2709_,
                    v___y_2718_,
                    v___y_2719_,
                    v___y_2720_,
                    v___y_2721_,
                );
                if crate::leanh::lean_obj_tag(v___x_2723_) == 0 {
                    v_a_2724_ = crate::leanh::lean_ctor_get(v___x_2723_, 0);
                    v_isSharedCheck_2893_ = (!crate::leanh::lean_is_exclusive(v___x_2723_)) as u8;
                    if v_isSharedCheck_2893_ == 0 {
                        v___x_2726_ = v___x_2723_;
                        v_isShared_2727_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2724_);
                        crate::leanh::lean_dec(v___x_2723_);
                        v___x_2726_ = crate::leanh::lean_box(0);
                        v_isShared_2727_ = v_isSharedCheck_2893_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2710_);
                    crate::leanh::lean_dec(v_goal_2709_);
                    v_a_2894_ = crate::leanh::lean_ctor_get(v___x_2723_, 0);
                    v_isSharedCheck_2901_ = (!crate::leanh::lean_is_exclusive(v___x_2723_)) as u8;
                    if v_isSharedCheck_2901_ == 0 {
                        v___x_2896_ = v___x_2723_;
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2894_);
                        crate::leanh::lean_dec(v___x_2723_);
                        v___x_2896_ = crate::leanh::lean_box(0);
                        v_isShared_2897_ = v_isSharedCheck_2901_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2733_ = l_Lean_Expr_cleanupAnnotations(v_a_2724_);
                v___x_2734_ = l_Lean_Expr_isApp(v___x_2733_);
                if v___x_2734_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2733_);
                    crate::leanh::lean_dec_ref(v___f_2710_);
                    crate::leanh::lean_dec(v_goal_2709_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2735_ = crate::leanh::lean_ctor_get(v___x_2733_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2735_);
                    v___x_2736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2733_);
                    v___x_2737_ = l_Lean_Expr_isApp(v___x_2736_);
                    if v___x_2737_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2736_);
                        crate::leanh::lean_dec_ref(v_arg_2735_);
                        crate::leanh::lean_dec_ref(v___f_2710_);
                        crate::leanh::lean_dec(v_goal_2709_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2738_ = crate::leanh::lean_ctor_get(v___x_2736_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2738_);
                        v___x_2739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2736_);
                        v___x_2740_ = l_Lean_Expr_isApp(v___x_2739_);
                        if v___x_2740_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2739_);
                            crate::leanh::lean_dec_ref(v_arg_2738_);
                            crate::leanh::lean_dec_ref(v_arg_2735_);
                            crate::leanh::lean_dec_ref(v___f_2710_);
                            crate::leanh::lean_dec(v_goal_2709_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2741_ = crate::leanh::lean_ctor_get(v___x_2739_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2741_);
                            v___x_2742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2739_);
                            v___x_2743_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___closed__1;
                            v___x_2744_ = l_Lean_Expr_isConstOf(v___x_2742_, v___x_2743_);
                            if v___x_2744_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2742_);
                                crate::leanh::lean_dec_ref(v_arg_2741_);
                                crate::leanh::lean_dec_ref(v_arg_2738_);
                                crate::leanh::lean_dec_ref(v_arg_2735_);
                                crate::leanh::lean_dec_ref(v___f_2710_);
                                crate::leanh::lean_dec(v_goal_2709_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_2726_);
                                v___x_2745_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                    v_arg_2738_,
                                    v___y_2716_,
                                    v___y_2717_,
                                    v___y_2718_,
                                    v___y_2719_,
                                    v___y_2720_,
                                    v___y_2721_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2745_) == 0 {
                                    v_a_2746_ = crate::leanh::lean_ctor_get(v___x_2745_, 0);
                                    crate::leanh::lean_inc(v_a_2746_);
                                    crate::leanh::lean_dec_ref_known(v___x_2745_, 1);
                                    v___x_2747_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                        v_arg_2735_,
                                        v___y_2716_,
                                        v___y_2717_,
                                        v___y_2718_,
                                        v___y_2719_,
                                        v___y_2720_,
                                        v___y_2721_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2747_) == 0 {
                                        v_a_2748_ = crate::leanh::lean_ctor_get(v___x_2747_, 0);
                                        crate::leanh::lean_inc(v_a_2748_);
                                        crate::leanh::lean_dec_ref_known(v___x_2747_, 1);
                                        v___x_2749_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_2742_, v_arg_2741_, v_a_2746_, v_a_2748_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
                                        if crate::leanh::lean_obj_tag(v___x_2749_) == 0 {
                                            v_a_2750_ = crate::leanh::lean_ctor_get(v___x_2749_, 0);
                                            crate::leanh::lean_inc(v_a_2750_);
                                            crate::leanh::lean_dec_ref_known(v___x_2749_, 1);
                                            v___x_2751_ = l_Lean_MVarId_replaceTargetDefEq(
                                                v_goal_2709_,
                                                v_a_2750_,
                                                v___y_2718_,
                                                v___y_2719_,
                                                v___y_2720_,
                                                v___y_2721_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2751_) == 0 {
                                                v_a_2752_ =
                                                    crate::leanh::lean_ctor_get(v___x_2751_, 0);
                                                v_isSharedCheck_2860_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2751_))
                                                        as u8;
                                                if v_isSharedCheck_2860_ == 0 {
                                                    v___x_2754_ = v___x_2751_;
                                                    v_isShared_2755_ = v_isSharedCheck_2860_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2752_);
                                                    crate::leanh::lean_dec(v___x_2751_);
                                                    v___x_2754_ = crate::leanh::lean_box(0);
                                                    v_isShared_2755_ = v_isSharedCheck_2860_;
                                                    state = 4;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___f_2710_);
                                                v_a_2861_ =
                                                    crate::leanh::lean_ctor_get(v___x_2751_, 0);
                                                v_isSharedCheck_2868_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2751_))
                                                        as u8;
                                                if v_isSharedCheck_2868_ == 0 {
                                                    v___x_2863_ = v___x_2751_;
                                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2861_);
                                                    crate::leanh::lean_dec(v___x_2751_);
                                                    v___x_2863_ = crate::leanh::lean_box(0);
                                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                                    state = 18;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___f_2710_);
                                            crate::leanh::lean_dec(v_goal_2709_);
                                            v_a_2869_ = crate::leanh::lean_ctor_get(v___x_2749_, 0);
                                            v_isSharedCheck_2876_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2749_))
                                                    as u8;
                                            if v_isSharedCheck_2876_ == 0 {
                                                v___x_2871_ = v___x_2749_;
                                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                                state = 20;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2869_);
                                                crate::leanh::lean_dec(v___x_2749_);
                                                v___x_2871_ = crate::leanh::lean_box(0);
                                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                                state = 20;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2746_);
                                        crate::leanh::lean_dec_ref(v___x_2742_);
                                        crate::leanh::lean_dec_ref(v_arg_2741_);
                                        crate::leanh::lean_dec_ref(v___f_2710_);
                                        crate::leanh::lean_dec(v_goal_2709_);
                                        v_a_2877_ = crate::leanh::lean_ctor_get(v___x_2747_, 0);
                                        v_isSharedCheck_2884_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2747_)) as u8;
                                        if v_isSharedCheck_2884_ == 0 {
                                            v___x_2879_ = v___x_2747_;
                                            v_isShared_2880_ = v_isSharedCheck_2884_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2877_);
                                            crate::leanh::lean_dec(v___x_2747_);
                                            v___x_2879_ = crate::leanh::lean_box(0);
                                            v_isShared_2880_ = v_isSharedCheck_2884_;
                                            state = 22;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2742_);
                                    crate::leanh::lean_dec_ref(v_arg_2741_);
                                    crate::leanh::lean_dec_ref(v_arg_2735_);
                                    crate::leanh::lean_dec_ref(v___f_2710_);
                                    crate::leanh::lean_dec(v_goal_2709_);
                                    v_a_2885_ = crate::leanh::lean_ctor_get(v___x_2745_, 0);
                                    v_isSharedCheck_2892_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2745_)) as u8;
                                    if v_isSharedCheck_2892_ == 0 {
                                        v___x_2887_ = v___x_2745_;
                                        v_isShared_2888_ = v_isSharedCheck_2892_;
                                        state = 24;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2885_);
                                        crate::leanh::lean_dec(v___x_2745_);
                                        v___x_2887_ = crate::leanh::lean_box(0);
                                        v_isShared_2888_ = v_isSharedCheck_2892_;
                                        state = 24;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2729_ = crate::leanh::lean_box(0);
                if v_isShared_2727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2726_, 0, v___x_2729_);
                    v___x_2731_ = v___x_2726_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2731_;
            }
            4 => {
                v_exceptCondsEntailsRflRule_2761_ = crate::leanh::lean_ctor_get(v___y_2711_, 10);
                v_exceptCondsEntailsPureRule_2762_ = crate::leanh::lean_ctor_get(v___y_2711_, 11);
                v_exceptCondsEntailsFalseRule_2763_ = crate::leanh::lean_ctor_get(v___y_2711_, 12);
                v_exceptCondsEntailsTrueRule_2764_ = crate::leanh::lean_ctor_get(v___y_2711_, 13);
                v___x_2765_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_a_2752_);
                crate::leanh::lean_inc_ref(v_exceptCondsEntailsPureRule_2762_);
                v___x_2819_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_exceptCondsEntailsPureRule_2762_,
                        v_a_2752_,
                        v___x_2765_,
                        v___y_2711_,
                        v___y_2712_,
                        v___y_2713_,
                        v___y_2714_,
                        v___y_2715_,
                        v___y_2716_,
                        v___y_2717_,
                        v___y_2718_,
                        v___y_2719_,
                        v___y_2720_,
                        v___y_2721_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2819_) == 0 {
                    v_a_2820_ = crate::leanh::lean_ctor_get(v___x_2819_, 0);
                    crate::leanh::lean_inc(v_a_2820_);
                    crate::leanh::lean_dec_ref_known(v___x_2819_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2820_) == 1 {
                        v_mvarIds_2849_ = crate::leanh::lean_ctor_get(v_a_2820_, 0);
                        crate::leanh::lean_inc(v_mvarIds_2849_);
                        crate::leanh::lean_dec_ref_known(v_a_2820_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_2849_) == 0 {
                            crate::leanh::lean_del_object(v___x_2754_);
                            crate::leanh::lean_dec(v_a_2752_);
                            v___x_2850_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_2721_);
                            crate::leanh::lean_inc_ref(v___y_2720_);
                            crate::leanh::lean_inc(v___y_2719_);
                            crate::leanh::lean_inc_ref(v___y_2718_);
                            crate::leanh::lean_inc(v___y_2717_);
                            crate::leanh::lean_inc_ref(v___y_2716_);
                            crate::leanh::lean_inc(v___y_2715_);
                            crate::leanh::lean_inc_ref(v___y_2714_);
                            crate::leanh::lean_inc(v___y_2713_);
                            crate::leanh::lean_inc(v___y_2712_);
                            crate::leanh::lean_inc_ref(v___y_2711_);
                            v___x_2851_ = crate::leanh::lean_apply_13(
                                v___f_2710_,
                                v___x_2850_,
                                v___y_2711_,
                                v___y_2712_,
                                v___y_2713_,
                                v___y_2714_,
                                v___y_2715_,
                                v___y_2716_,
                                v___y_2717_,
                                v___y_2718_,
                                v___y_2719_,
                                v___y_2720_,
                                v___y_2721_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_2851_;
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_2849_);
                            v___y_2822_ = v___y_2711_;
                            v_exceptCondsEntailsRflRule_2823_ = v_exceptCondsEntailsRflRule_2761_;
                            v_exceptCondsEntailsFalseRule_2824_ =
                                v_exceptCondsEntailsFalseRule_2763_;
                            v_exceptCondsEntailsTrueRule_2825_ = v_exceptCondsEntailsTrueRule_2764_;
                            v___y_2826_ = v___y_2712_;
                            v___y_2827_ = v___y_2713_;
                            v___y_2828_ = v___y_2714_;
                            v___y_2829_ = v___y_2715_;
                            v___y_2830_ = v___y_2716_;
                            v___y_2831_ = v___y_2717_;
                            v___y_2832_ = v___y_2718_;
                            v___y_2833_ = v___y_2719_;
                            v___y_2834_ = v___y_2720_;
                            v___y_2835_ = v___y_2721_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2820_);
                        v___y_2822_ = v___y_2711_;
                        v_exceptCondsEntailsRflRule_2823_ = v_exceptCondsEntailsRflRule_2761_;
                        v_exceptCondsEntailsFalseRule_2824_ = v_exceptCondsEntailsFalseRule_2763_;
                        v_exceptCondsEntailsTrueRule_2825_ = v_exceptCondsEntailsTrueRule_2764_;
                        v___y_2826_ = v___y_2712_;
                        v___y_2827_ = v___y_2713_;
                        v___y_2828_ = v___y_2714_;
                        v___y_2829_ = v___y_2715_;
                        v___y_2830_ = v___y_2716_;
                        v___y_2831_ = v___y_2717_;
                        v___y_2832_ = v___y_2718_;
                        v___y_2833_ = v___y_2719_;
                        v___y_2834_ = v___y_2720_;
                        v___y_2835_ = v___y_2721_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2754_);
                    crate::leanh::lean_dec(v_a_2752_);
                    crate::leanh::lean_dec_ref(v___f_2710_);
                    v_a_2852_ = crate::leanh::lean_ctor_get(v___x_2819_, 0);
                    v_isSharedCheck_2859_ = (!crate::leanh::lean_is_exclusive(v___x_2819_)) as u8;
                    if v_isSharedCheck_2859_ == 0 {
                        v___x_2854_ = v___x_2819_;
                        v_isShared_2855_ = v_isSharedCheck_2859_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2852_);
                        crate::leanh::lean_dec(v___x_2819_);
                        v___x_2854_ = crate::leanh::lean_box(0);
                        v_isShared_2855_ = v_isSharedCheck_2859_;
                        state = 16;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2757_, 0, v_a_2752_);
                if v_isShared_2755_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2754_, 0, v___x_2757_);
                    v___x_2759_ = v___x_2754_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
                    v___x_2759_ = v_reuseFailAlloc_2760_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2759_;
            }
            7 => {
                crate::leanh::lean_inc(v_a_2752_);
                crate::leanh::lean_inc_ref(v_exceptCondsEntailsRflRule_2768_);
                v___x_2779_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_exceptCondsEntailsRflRule_2768_,
                        v_a_2752_,
                        v___x_2765_,
                        v___y_2767_,
                        v___y_2769_,
                        v___y_2770_,
                        v___y_2771_,
                        v___y_2772_,
                        v___y_2773_,
                        v___y_2774_,
                        v___y_2775_,
                        v___y_2776_,
                        v___y_2777_,
                        v___y_2778_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2779_) == 0 {
                    v_a_2780_ = crate::leanh::lean_ctor_get(v___x_2779_, 0);
                    crate::leanh::lean_inc(v_a_2780_);
                    crate::leanh::lean_dec_ref_known(v___x_2779_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2780_) == 1 {
                        v_mvarIds_2781_ = crate::leanh::lean_ctor_get(v_a_2780_, 0);
                        crate::leanh::lean_inc(v_mvarIds_2781_);
                        crate::leanh::lean_dec_ref_known(v_a_2780_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_2781_) == 0 {
                            crate::leanh::lean_del_object(v___x_2754_);
                            crate::leanh::lean_dec(v_a_2752_);
                            v___x_2782_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_2778_);
                            crate::leanh::lean_inc_ref(v___y_2777_);
                            crate::leanh::lean_inc(v___y_2776_);
                            crate::leanh::lean_inc_ref(v___y_2775_);
                            crate::leanh::lean_inc(v___y_2774_);
                            crate::leanh::lean_inc_ref(v___y_2773_);
                            crate::leanh::lean_inc(v___y_2772_);
                            crate::leanh::lean_inc_ref(v___y_2771_);
                            crate::leanh::lean_inc(v___y_2770_);
                            crate::leanh::lean_inc(v___y_2769_);
                            crate::leanh::lean_inc_ref(v___y_2767_);
                            v___x_2783_ = crate::leanh::lean_apply_13(
                                v___f_2710_,
                                v___x_2782_,
                                v___y_2767_,
                                v___y_2769_,
                                v___y_2770_,
                                v___y_2771_,
                                v___y_2772_,
                                v___y_2773_,
                                v___y_2774_,
                                v___y_2775_,
                                v___y_2776_,
                                v___y_2777_,
                                v___y_2778_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_2783_;
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_2781_);
                            crate::leanh::lean_dec_ref(v___f_2710_);
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2780_);
                        crate::leanh::lean_dec_ref(v___f_2710_);
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2754_);
                    crate::leanh::lean_dec(v_a_2752_);
                    crate::leanh::lean_dec_ref(v___f_2710_);
                    v_a_2784_ = crate::leanh::lean_ctor_get(v___x_2779_, 0);
                    v_isSharedCheck_2791_ = (!crate::leanh::lean_is_exclusive(v___x_2779_)) as u8;
                    if v_isSharedCheck_2791_ == 0 {
                        v___x_2786_ = v___x_2779_;
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2784_);
                        crate::leanh::lean_dec(v___x_2779_);
                        v___x_2786_ = crate::leanh::lean_box(0);
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2787_ == 0 {
                    v___x_2789_ = v___x_2786_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2789_;
            }
            10 => {
                crate::leanh::lean_inc(v_a_2752_);
                crate::leanh::lean_inc_ref(v_exceptCondsEntailsTrueRule_2795_);
                v___x_2806_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_exceptCondsEntailsTrueRule_2795_,
                        v_a_2752_,
                        v___x_2765_,
                        v___y_2793_,
                        v___y_2796_,
                        v___y_2797_,
                        v___y_2798_,
                        v___y_2799_,
                        v___y_2800_,
                        v___y_2801_,
                        v___y_2802_,
                        v___y_2803_,
                        v___y_2804_,
                        v___y_2805_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2806_) == 0 {
                    v_a_2807_ = crate::leanh::lean_ctor_get(v___x_2806_, 0);
                    crate::leanh::lean_inc(v_a_2807_);
                    crate::leanh::lean_dec_ref_known(v___x_2806_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2807_) == 1 {
                        v_mvarIds_2808_ = crate::leanh::lean_ctor_get(v_a_2807_, 0);
                        crate::leanh::lean_inc(v_mvarIds_2808_);
                        crate::leanh::lean_dec_ref_known(v_a_2807_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_2808_) == 0 {
                            crate::leanh::lean_del_object(v___x_2754_);
                            crate::leanh::lean_dec(v_a_2752_);
                            v___x_2809_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_2805_);
                            crate::leanh::lean_inc_ref(v___y_2804_);
                            crate::leanh::lean_inc(v___y_2803_);
                            crate::leanh::lean_inc_ref(v___y_2802_);
                            crate::leanh::lean_inc(v___y_2801_);
                            crate::leanh::lean_inc_ref(v___y_2800_);
                            crate::leanh::lean_inc(v___y_2799_);
                            crate::leanh::lean_inc_ref(v___y_2798_);
                            crate::leanh::lean_inc(v___y_2797_);
                            crate::leanh::lean_inc(v___y_2796_);
                            crate::leanh::lean_inc_ref(v___y_2793_);
                            v___x_2810_ = crate::leanh::lean_apply_13(
                                v___f_2710_,
                                v___x_2809_,
                                v___y_2793_,
                                v___y_2796_,
                                v___y_2797_,
                                v___y_2798_,
                                v___y_2799_,
                                v___y_2800_,
                                v___y_2801_,
                                v___y_2802_,
                                v___y_2803_,
                                v___y_2804_,
                                v___y_2805_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_2810_;
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_2808_);
                            v___y_2767_ = v___y_2793_;
                            v_exceptCondsEntailsRflRule_2768_ = v_exceptCondsEntailsRflRule_2794_;
                            v___y_2769_ = v___y_2796_;
                            v___y_2770_ = v___y_2797_;
                            v___y_2771_ = v___y_2798_;
                            v___y_2772_ = v___y_2799_;
                            v___y_2773_ = v___y_2800_;
                            v___y_2774_ = v___y_2801_;
                            v___y_2775_ = v___y_2802_;
                            v___y_2776_ = v___y_2803_;
                            v___y_2777_ = v___y_2804_;
                            v___y_2778_ = v___y_2805_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2807_);
                        v___y_2767_ = v___y_2793_;
                        v_exceptCondsEntailsRflRule_2768_ = v_exceptCondsEntailsRflRule_2794_;
                        v___y_2769_ = v___y_2796_;
                        v___y_2770_ = v___y_2797_;
                        v___y_2771_ = v___y_2798_;
                        v___y_2772_ = v___y_2799_;
                        v___y_2773_ = v___y_2800_;
                        v___y_2774_ = v___y_2801_;
                        v___y_2775_ = v___y_2802_;
                        v___y_2776_ = v___y_2803_;
                        v___y_2777_ = v___y_2804_;
                        v___y_2778_ = v___y_2805_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2754_);
                    crate::leanh::lean_dec(v_a_2752_);
                    crate::leanh::lean_dec_ref(v___f_2710_);
                    v_a_2811_ = crate::leanh::lean_ctor_get(v___x_2806_, 0);
                    v_isSharedCheck_2818_ = (!crate::leanh::lean_is_exclusive(v___x_2806_)) as u8;
                    if v_isSharedCheck_2818_ == 0 {
                        v___x_2813_ = v___x_2806_;
                        v_isShared_2814_ = v_isSharedCheck_2818_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2811_);
                        crate::leanh::lean_dec(v___x_2806_);
                        v___x_2813_ = crate::leanh::lean_box(0);
                        v_isShared_2814_ = v_isSharedCheck_2818_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_2814_ == 0 {
                    v___x_2816_ = v___x_2813_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
                    v___x_2816_ = v_reuseFailAlloc_2817_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2816_;
            }
            13 => {
                crate::leanh::lean_inc(v_a_2752_);
                crate::leanh::lean_inc_ref(v_exceptCondsEntailsFalseRule_2824_);
                v___x_2836_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_exceptCondsEntailsFalseRule_2824_,
                        v_a_2752_,
                        v___x_2765_,
                        v___y_2822_,
                        v___y_2826_,
                        v___y_2827_,
                        v___y_2828_,
                        v___y_2829_,
                        v___y_2830_,
                        v___y_2831_,
                        v___y_2832_,
                        v___y_2833_,
                        v___y_2834_,
                        v___y_2835_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2836_) == 0 {
                    v_a_2837_ = crate::leanh::lean_ctor_get(v___x_2836_, 0);
                    crate::leanh::lean_inc(v_a_2837_);
                    crate::leanh::lean_dec_ref_known(v___x_2836_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2837_) == 1 {
                        v_mvarIds_2838_ = crate::leanh::lean_ctor_get(v_a_2837_, 0);
                        crate::leanh::lean_inc(v_mvarIds_2838_);
                        crate::leanh::lean_dec_ref_known(v_a_2837_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_2838_) == 0 {
                            crate::leanh::lean_del_object(v___x_2754_);
                            crate::leanh::lean_dec(v_a_2752_);
                            v___x_2839_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_2835_);
                            crate::leanh::lean_inc_ref(v___y_2834_);
                            crate::leanh::lean_inc(v___y_2833_);
                            crate::leanh::lean_inc_ref(v___y_2832_);
                            crate::leanh::lean_inc(v___y_2831_);
                            crate::leanh::lean_inc_ref(v___y_2830_);
                            crate::leanh::lean_inc(v___y_2829_);
                            crate::leanh::lean_inc_ref(v___y_2828_);
                            crate::leanh::lean_inc(v___y_2827_);
                            crate::leanh::lean_inc(v___y_2826_);
                            crate::leanh::lean_inc_ref(v___y_2822_);
                            v___x_2840_ = crate::leanh::lean_apply_13(
                                v___f_2710_,
                                v___x_2839_,
                                v___y_2822_,
                                v___y_2826_,
                                v___y_2827_,
                                v___y_2828_,
                                v___y_2829_,
                                v___y_2830_,
                                v___y_2831_,
                                v___y_2832_,
                                v___y_2833_,
                                v___y_2834_,
                                v___y_2835_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_2840_;
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_2838_);
                            v___y_2793_ = v___y_2822_;
                            v_exceptCondsEntailsRflRule_2794_ = v_exceptCondsEntailsRflRule_2823_;
                            v_exceptCondsEntailsTrueRule_2795_ = v_exceptCondsEntailsTrueRule_2825_;
                            v___y_2796_ = v___y_2826_;
                            v___y_2797_ = v___y_2827_;
                            v___y_2798_ = v___y_2828_;
                            v___y_2799_ = v___y_2829_;
                            v___y_2800_ = v___y_2830_;
                            v___y_2801_ = v___y_2831_;
                            v___y_2802_ = v___y_2832_;
                            v___y_2803_ = v___y_2833_;
                            v___y_2804_ = v___y_2834_;
                            v___y_2805_ = v___y_2835_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2837_);
                        v___y_2793_ = v___y_2822_;
                        v_exceptCondsEntailsRflRule_2794_ = v_exceptCondsEntailsRflRule_2823_;
                        v_exceptCondsEntailsTrueRule_2795_ = v_exceptCondsEntailsTrueRule_2825_;
                        v___y_2796_ = v___y_2826_;
                        v___y_2797_ = v___y_2827_;
                        v___y_2798_ = v___y_2828_;
                        v___y_2799_ = v___y_2829_;
                        v___y_2800_ = v___y_2830_;
                        v___y_2801_ = v___y_2831_;
                        v___y_2802_ = v___y_2832_;
                        v___y_2803_ = v___y_2833_;
                        v___y_2804_ = v___y_2834_;
                        v___y_2805_ = v___y_2835_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2754_);
                    crate::leanh::lean_dec(v_a_2752_);
                    crate::leanh::lean_dec_ref(v___f_2710_);
                    v_a_2841_ = crate::leanh::lean_ctor_get(v___x_2836_, 0);
                    v_isSharedCheck_2848_ = (!crate::leanh::lean_is_exclusive(v___x_2836_)) as u8;
                    if v_isSharedCheck_2848_ == 0 {
                        v___x_2843_ = v___x_2836_;
                        v_isShared_2844_ = v_isSharedCheck_2848_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2841_);
                        crate::leanh::lean_dec(v___x_2836_);
                        v___x_2843_ = crate::leanh::lean_box(0);
                        v_isShared_2844_ = v_isSharedCheck_2848_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2844_ == 0 {
                    v___x_2846_ = v___x_2843_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
                    v___x_2846_ = v_reuseFailAlloc_2847_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2846_;
            }
            16 => {
                if v_isShared_2855_ == 0 {
                    v___x_2857_ = v___x_2854_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
                    v___x_2857_ = v_reuseFailAlloc_2858_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2857_;
            }
            18 => {
                if v_isShared_2864_ == 0 {
                    v___x_2866_ = v___x_2863_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2866_;
            }
            20 => {
                if v_isShared_2872_ == 0 {
                    v___x_2874_ = v___x_2871_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
                    v___x_2874_ = v_reuseFailAlloc_2875_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2874_;
            }
            22 => {
                if v_isShared_2880_ == 0 {
                    v___x_2882_ = v___x_2879_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
                    v___x_2882_ = v_reuseFailAlloc_2883_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2882_;
            }
            24 => {
                if v_isShared_2888_ == 0 {
                    v___x_2890_ = v___x_2887_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
                    v___x_2890_ = v_reuseFailAlloc_2891_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2890_;
            }
            26 => {
                if v_isShared_2897_ == 0 {
                    v___x_2899_ = v___x_2896_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
                    v___x_2899_ = v_reuseFailAlloc_2900_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___boxed(
    mut v_goal_2902_: *mut crate::leanh::LeanObject,
    mut v___f_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
    mut v___y_2906_: *mut crate::leanh::LeanObject,
    mut v___y_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1(
        v_goal_2902_,
        v___f_2903_,
        v___y_2904_,
        v___y_2905_,
        v___y_2906_,
        v___y_2907_,
        v___y_2908_,
        v___y_2909_,
        v___y_2910_,
        v___y_2911_,
        v___y_2912_,
        v___y_2913_,
        v___y_2914_,
    );
    crate::leanh::lean_dec(v___y_2914_);
    crate::leanh::lean_dec_ref(v___y_2913_);
    crate::leanh::lean_dec(v___y_2912_);
    crate::leanh::lean_dec_ref(v___y_2911_);
    crate::leanh::lean_dec(v___y_2910_);
    crate::leanh::lean_dec_ref(v___y_2909_);
    crate::leanh::lean_dec(v___y_2908_);
    crate::leanh::lean_dec_ref(v___y_2907_);
    crate::leanh::lean_dec(v___y_2906_);
    crate::leanh::lean_dec(v___y_2905_);
    crate::leanh::lean_dec_ref(v___y_2904_);
    return v_res_2916_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails(
    mut v_goal_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_a_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
    mut v_a_2924_: *mut crate::leanh::LeanObject,
    mut v_a_2925_: *mut crate::leanh::LeanObject,
    mut v_a_2926_: *mut crate::leanh::LeanObject,
    mut v_a_2927_: *mut crate::leanh::LeanObject,
    mut v_a_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2931_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___closed__0;
    crate::leanh::lean_inc(v_goal_2918_);
    v___f_2932_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___lam__1___boxed
            as *mut core::ffi::c_void,
        14,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2932_, 0, v_goal_2918_);
    crate::leanh::lean_closure_set(v___f_2932_, 1, v___f_2931_);
    v___x_2933_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_2918_, v___f_2932_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
    return v___x_2933_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___boxed(
    mut v_goal_2934_: *mut crate::leanh::LeanObject,
    mut v_a_2935_: *mut crate::leanh::LeanObject,
    mut v_a_2936_: *mut crate::leanh::LeanObject,
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_a_2938_: *mut crate::leanh::LeanObject,
    mut v_a_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
    mut v_a_2941_: *mut crate::leanh::LeanObject,
    mut v_a_2942_: *mut crate::leanh::LeanObject,
    mut v_a_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2947_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails(
        v_goal_2934_,
        v_a_2935_,
        v_a_2936_,
        v_a_2937_,
        v_a_2938_,
        v_a_2939_,
        v_a_2940_,
        v_a_2941_,
        v_a_2942_,
        v_a_2943_,
        v_a_2944_,
        v_a_2945_,
    );
    crate::leanh::lean_dec(v_a_2945_);
    crate::leanh::lean_dec_ref(v_a_2944_);
    crate::leanh::lean_dec(v_a_2943_);
    crate::leanh::lean_dec_ref(v_a_2942_);
    crate::leanh::lean_dec(v_a_2941_);
    crate::leanh::lean_dec_ref(v_a_2940_);
    crate::leanh::lean_dec(v_a_2939_);
    crate::leanh::lean_dec_ref(v_a_2938_);
    crate::leanh::lean_dec(v_a_2937_);
    crate::leanh::lean_dec(v_a_2936_);
    crate::leanh::lean_dec_ref(v_a_2935_);
    return v_res_2947_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__0;
    v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
    return v___x_2950_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2952_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__2;
    v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
    return v___x_2953_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0(
    mut v_head_2954_: *mut crate::leanh::LeanObject,
    mut v___x_2955_: *mut crate::leanh::LeanObject,
    mut v___x_2956_: *mut crate::leanh::LeanObject,
    mut v___x_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
    mut v___y_2961_: *mut crate::leanh::LeanObject,
    mut v___y_2962_: *mut crate::leanh::LeanObject,
    mut v___y_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2984_: u8 = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v_arg_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: u8 = 0;
    let mut v_arg_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: u8 = 0;
    let mut v_arg_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v_a_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_a_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_a_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_head_2954_);
                v___x_2970_ = l_Lean_MVarId_getType(
                    v_head_2954_,
                    v___y_2965_,
                    v___y_2966_,
                    v___y_2967_,
                    v___y_2968_,
                );
                if crate::leanh::lean_obj_tag(v___x_2970_) == 0 {
                    v_a_2971_ = crate::leanh::lean_ctor_get(v___x_2970_, 0);
                    crate::leanh::lean_inc(v_a_2971_);
                    crate::leanh::lean_dec_ref_known(v___x_2970_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2971_) == 7 {
                        v_binderName_2981_ = crate::leanh::lean_ctor_get(v_a_2971_, 0);
                        v_binderType_2982_ = crate::leanh::lean_ctor_get(v_a_2971_, 1);
                        v_body_2983_ = crate::leanh::lean_ctor_get(v_a_2971_, 2);
                        v_binderInfo_2984_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_2971_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_inc_ref(v_body_2983_);
                        v___x_2985_ = l_Lean_Expr_cleanupAnnotations(v_body_2983_);
                        v___x_2986_ = l_Lean_Expr_isApp(v___x_2985_);
                        if v___x_2986_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2985_);
                            crate::leanh::lean_dec_ref(v___x_2957_);
                            crate::leanh::lean_dec_ref(v___x_2956_);
                            crate::leanh::lean_dec_ref(v___x_2955_);
                            crate::leanh::lean_dec(v_head_2954_);
                            v___y_2973_ = v___y_2965_;
                            v___y_2974_ = v___y_2966_;
                            v___y_2975_ = v___y_2967_;
                            v___y_2976_ = v___y_2968_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_2987_ = crate::leanh::lean_ctor_get(v___x_2985_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2987_);
                            v___x_2988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2985_);
                            v___x_2989_ = l_Lean_Expr_isApp(v___x_2988_);
                            if v___x_2989_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2988_);
                                crate::leanh::lean_dec_ref(v_arg_2987_);
                                crate::leanh::lean_dec_ref(v___x_2957_);
                                crate::leanh::lean_dec_ref(v___x_2956_);
                                crate::leanh::lean_dec_ref(v___x_2955_);
                                crate::leanh::lean_dec(v_head_2954_);
                                v___y_2973_ = v___y_2965_;
                                v___y_2974_ = v___y_2966_;
                                v___y_2975_ = v___y_2967_;
                                v___y_2976_ = v___y_2968_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_2990_ = crate::leanh::lean_ctor_get(v___x_2988_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2990_);
                                v___x_2991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2988_);
                                v___x_2992_ = l_Lean_Expr_isApp(v___x_2991_);
                                if v___x_2992_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2991_);
                                    crate::leanh::lean_dec_ref(v_arg_2990_);
                                    crate::leanh::lean_dec_ref(v_arg_2987_);
                                    crate::leanh::lean_dec_ref(v___x_2957_);
                                    crate::leanh::lean_dec_ref(v___x_2956_);
                                    crate::leanh::lean_dec_ref(v___x_2955_);
                                    crate::leanh::lean_dec(v_head_2954_);
                                    v___y_2973_ = v___y_2965_;
                                    v___y_2974_ = v___y_2966_;
                                    v___y_2975_ = v___y_2967_;
                                    v___y_2976_ = v___y_2968_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_2993_ = crate::leanh::lean_ctor_get(v___x_2991_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2993_);
                                    v___x_2994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2991_);
                                    v___x_2995_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__4;
                                    v___x_2996_ = l_Lean_Name_mkStr4(
                                        v___x_2955_,
                                        v___x_2956_,
                                        v___x_2995_,
                                        v___x_2957_,
                                    );
                                    v___x_2997_ = l_Lean_Expr_isConstOf(v___x_2994_, v___x_2996_);
                                    crate::leanh::lean_dec(v___x_2996_);
                                    if v___x_2997_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2994_);
                                        crate::leanh::lean_dec_ref(v_arg_2993_);
                                        crate::leanh::lean_dec_ref(v_arg_2990_);
                                        crate::leanh::lean_dec_ref(v_arg_2987_);
                                        crate::leanh::lean_dec(v_head_2954_);
                                        v___y_2973_ = v___y_2965_;
                                        v___y_2974_ = v___y_2966_;
                                        v___y_2975_ = v___y_2967_;
                                        v___y_2976_ = v___y_2968_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc_ref(v_binderType_2982_);
                                        crate::leanh::lean_inc(v_binderName_2981_);
                                        crate::leanh::lean_dec_ref_known(v_a_2971_, 3);
                                        v___x_2998_ = l_Lean_Meta_Sym_unfoldReducible(
                                            v_arg_2993_,
                                            v___y_2965_,
                                            v___y_2966_,
                                            v___y_2967_,
                                            v___y_2968_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2998_) == 0 {
                                            v_a_2999_ = crate::leanh::lean_ctor_get(v___x_2998_, 0);
                                            crate::leanh::lean_inc(v_a_2999_);
                                            crate::leanh::lean_dec_ref_known(v___x_2998_, 1);
                                            v___x_3000_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                                v_a_2999_,
                                                v___y_2964_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_3000_) == 0 {
                                                v_a_3001_ =
                                                    crate::leanh::lean_ctor_get(v___x_3000_, 0);
                                                crate::leanh::lean_inc(v_a_3001_);
                                                crate::leanh::lean_dec_ref_known(v___x_3000_, 1);
                                                v___x_3002_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__1(v___x_2994_, v_a_3001_, v_arg_2990_, v_arg_2987_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
                                                if crate::leanh::lean_obj_tag(v___x_3002_) == 0 {
                                                    v_a_3003_ =
                                                        crate::leanh::lean_ctor_get(v___x_3002_, 0);
                                                    crate::leanh::lean_inc(v_a_3003_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3002_,
                                                        1,
                                                    );
                                                    v___x_3004_ = l_Lean_Expr_forallE___override(
                                                        v_binderName_2981_,
                                                        v_binderType_2982_,
                                                        v_a_3003_,
                                                        v_binderInfo_2984_,
                                                    );
                                                    v___x_3005_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3004_, v___y_2964_);
                                                    if crate::leanh::lean_obj_tag(v___x_3005_) == 0
                                                    {
                                                        v_a_3006_ = crate::leanh::lean_ctor_get(
                                                            v___x_3005_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_3006_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_3005_,
                                                            1,
                                                        );
                                                        v___x_3007_ =
                                                            l_Lean_MVarId_replaceTargetDefEq(
                                                                v_head_2954_,
                                                                v_a_3006_,
                                                                v___y_2965_,
                                                                v___y_2966_,
                                                                v___y_2967_,
                                                                v___y_2968_,
                                                            );
                                                        return v___x_3007_;
                                                    } else {
                                                        crate::leanh::lean_dec(v_head_2954_);
                                                        v_a_3008_ = crate::leanh::lean_ctor_get(
                                                            v___x_3005_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3015_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_3005_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3015_ == 0 {
                                                            v___x_3010_ = v___x_3005_;
                                                            v_isShared_3011_ =
                                                                v_isSharedCheck_3015_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_3008_);
                                                            crate::leanh::lean_dec(v___x_3005_);
                                                            v___x_3010_ = crate::leanh::lean_box(0);
                                                            v_isShared_3011_ =
                                                                v_isSharedCheck_3015_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_binderType_2982_);
                                                    crate::leanh::lean_dec(v_binderName_2981_);
                                                    crate::leanh::lean_dec(v_head_2954_);
                                                    v_a_3016_ =
                                                        crate::leanh::lean_ctor_get(v___x_3002_, 0);
                                                    v_isSharedCheck_3023_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3002_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3023_ == 0 {
                                                        v___x_3018_ = v___x_3002_;
                                                        v_isShared_3019_ = v_isSharedCheck_3023_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_3016_);
                                                        crate::leanh::lean_dec(v___x_3002_);
                                                        v___x_3018_ = crate::leanh::lean_box(0);
                                                        v_isShared_3019_ = v_isSharedCheck_3023_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_2994_);
                                                crate::leanh::lean_dec_ref(v_arg_2990_);
                                                crate::leanh::lean_dec_ref(v_arg_2987_);
                                                crate::leanh::lean_dec_ref(v_binderType_2982_);
                                                crate::leanh::lean_dec(v_binderName_2981_);
                                                crate::leanh::lean_dec(v_head_2954_);
                                                v_a_3024_ =
                                                    crate::leanh::lean_ctor_get(v___x_3000_, 0);
                                                v_isSharedCheck_3031_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3000_))
                                                        as u8;
                                                if v_isSharedCheck_3031_ == 0 {
                                                    v___x_3026_ = v___x_3000_;
                                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3024_);
                                                    crate::leanh::lean_dec(v___x_3000_);
                                                    v___x_3026_ = crate::leanh::lean_box(0);
                                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2994_);
                                            crate::leanh::lean_dec_ref(v_arg_2990_);
                                            crate::leanh::lean_dec_ref(v_arg_2987_);
                                            crate::leanh::lean_dec_ref(v_binderType_2982_);
                                            crate::leanh::lean_dec(v_binderName_2981_);
                                            crate::leanh::lean_dec(v_head_2954_);
                                            v_a_3032_ = crate::leanh::lean_ctor_get(v___x_2998_, 0);
                                            v_isSharedCheck_3039_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2998_))
                                                    as u8;
                                            if v_isSharedCheck_3039_ == 0 {
                                                v___x_3034_ = v___x_2998_;
                                                v_isShared_3035_ = v_isSharedCheck_3039_;
                                                state = 8;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3032_);
                                                crate::leanh::lean_dec(v___x_2998_);
                                                v___x_3034_ = crate::leanh::lean_box(0);
                                                v_isShared_3035_ = v_isSharedCheck_3039_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2957_);
                        crate::leanh::lean_dec_ref(v___x_2956_);
                        crate::leanh::lean_dec_ref(v___x_2955_);
                        crate::leanh::lean_dec(v_head_2954_);
                        v___x_3040_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__3);
                        v___x_3041_ = l_Lean_MessageData_ofExpr(v_a_2971_);
                        v___x_3042_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3042_, 0, v___x_3040_);
                        crate::leanh::lean_ctor_set(v___x_3042_, 1, v___x_3041_);
                        v___x_3043_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3042_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
                        return v___x_3043_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2957_);
                    crate::leanh::lean_dec_ref(v___x_2956_);
                    crate::leanh::lean_dec_ref(v___x_2955_);
                    crate::leanh::lean_dec(v_head_2954_);
                    v_a_3044_ = crate::leanh::lean_ctor_get(v___x_2970_, 0);
                    v_isSharedCheck_3051_ = (!crate::leanh::lean_is_exclusive(v___x_2970_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v___x_3046_ = v___x_2970_;
                        v_isShared_3047_ = v_isSharedCheck_3051_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3044_);
                        crate::leanh::lean_dec(v___x_2970_);
                        v___x_3046_ = crate::leanh::lean_box(0);
                        v_isShared_3047_ = v_isSharedCheck_3051_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2977_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1);
                v___x_2978_ = l_Lean_MessageData_ofExpr(v_a_2971_);
                v___x_2979_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2979_, 0, v___x_2977_);
                crate::leanh::lean_ctor_set(v___x_2979_, 1, v___x_2978_);
                v___x_2980_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_2979_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
                return v___x_2980_;
            }
            2 => {
                if v_isShared_3011_ == 0 {
                    v___x_3013_ = v___x_3010_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
                    v___x_3013_ = v_reuseFailAlloc_3014_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3013_;
            }
            4 => {
                if v_isShared_3019_ == 0 {
                    v___x_3021_ = v___x_3018_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
                    v___x_3021_ = v_reuseFailAlloc_3022_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3021_;
            }
            6 => {
                if v_isShared_3027_ == 0 {
                    v___x_3029_ = v___x_3026_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
                    v___x_3029_ = v_reuseFailAlloc_3030_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3029_;
            }
            8 => {
                if v_isShared_3035_ == 0 {
                    v___x_3037_ = v___x_3034_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3037_;
            }
            10 => {
                if v_isShared_3047_ == 0 {
                    v___x_3049_ = v___x_3046_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
                    v___x_3049_ = v_reuseFailAlloc_3050_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3049_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___boxed(
    mut v_head_3052_: *mut crate::leanh::LeanObject,
    mut v___x_3053_: *mut crate::leanh::LeanObject,
    mut v___x_3054_: *mut crate::leanh::LeanObject,
    mut v___x_3055_: *mut crate::leanh::LeanObject,
    mut v___y_3056_: *mut crate::leanh::LeanObject,
    mut v___y_3057_: *mut crate::leanh::LeanObject,
    mut v___y_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0(
        v_head_3052_,
        v___x_3053_,
        v___x_3054_,
        v___x_3055_,
        v___y_3056_,
        v___y_3057_,
        v___y_3058_,
        v___y_3059_,
        v___y_3060_,
        v___y_3061_,
        v___y_3062_,
        v___y_3063_,
        v___y_3064_,
        v___y_3065_,
        v___y_3066_,
    );
    crate::leanh::lean_dec(v___y_3066_);
    crate::leanh::lean_dec_ref(v___y_3065_);
    crate::leanh::lean_dec(v___y_3064_);
    crate::leanh::lean_dec_ref(v___y_3063_);
    crate::leanh::lean_dec(v___y_3062_);
    crate::leanh::lean_dec_ref(v___y_3061_);
    crate::leanh::lean_dec(v___y_3060_);
    crate::leanh::lean_dec_ref(v___y_3059_);
    crate::leanh::lean_dec(v___y_3058_);
    crate::leanh::lean_dec(v___y_3057_);
    crate::leanh::lean_dec_ref(v___y_3056_);
    return v_res_3068_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3075_ = 0;
    v___x_3076_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1;
    v___x_3077_ = l_Lean_MessageData_ofConstName(v___x_3076_, v___x_3075_);
    return v___x_3077_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3078_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__2,
    );
    v___x_3079_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__1,
    );
    v___x_3080_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3080_, 0, v___x_3079_);
    crate::leanh::lean_ctor_set(v___x_3080_, 1, v___x_3078_);
    return v___x_3080_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3081_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_3082_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__3,
    );
    v___x_3083_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3083_, 0, v___x_3082_);
    crate::leanh::lean_ctor_set(v___x_3083_, 1, v___x_3081_);
    return v___x_3083_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3085_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__5;
    v___x_3086_ = l_Lean_stringToMessageData(v___x_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1(
    mut v_goal_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: u8 = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v_postCondEntailsRflRule_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postCondEntailsMkRule_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___y_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postCondEntailsMkRule_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3171_: u8 = 0;
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut v_a_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3198_: u8 = 0;
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_unused_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v_mvarIds_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v_a_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3224_: u8 = 0;
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v_a_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_3087_);
                v___x_3106_ = l_Lean_MVarId_getType(
                    v_goal_3087_,
                    v___y_3095_,
                    v___y_3096_,
                    v___y_3097_,
                    v___y_3098_,
                );
                if crate::leanh::lean_obj_tag(v___x_3106_) == 0 {
                    v_a_3107_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3229_ = (!crate::leanh::lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v___x_3109_ = v___x_3106_;
                        v_isShared_3110_ = v_isSharedCheck_3229_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3107_);
                        crate::leanh::lean_dec(v___x_3106_);
                        v___x_3109_ = crate::leanh::lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3229_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_3087_);
                    v_a_3230_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                    v_isSharedCheck_3237_ = (!crate::leanh::lean_is_exclusive(v___x_3106_)) as u8;
                    if v_isSharedCheck_3237_ == 0 {
                        v___x_3232_ = v___x_3106_;
                        v_isShared_3233_ = v_isSharedCheck_3237_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3230_);
                        crate::leanh::lean_dec(v___x_3106_);
                        v___x_3232_ = crate::leanh::lean_box(0);
                        v_isShared_3233_ = v_isSharedCheck_3237_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3103_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3103_, 0, v___y_3101_);
                crate::leanh::lean_ctor_set(v___x_3103_, 1, v___y_3102_);
                v___x_3104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3104_, 0, v___x_3103_);
                v___x_3105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3105_, 0, v___x_3104_);
                return v___x_3105_;
            }
            2 => {
                crate::leanh::lean_inc(v_a_3107_);
                v___x_3127_ = l_Lean_Expr_cleanupAnnotations(v_a_3107_);
                v___x_3128_ = l_Lean_Expr_isApp(v___x_3127_);
                if v___x_3128_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3127_);
                    crate::leanh::lean_dec(v_a_3107_);
                    crate::leanh::lean_dec(v_goal_3087_);
                    state = 3;
                    continue;
                } else {
                    v___x_3129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3127_);
                    v___x_3130_ = l_Lean_Expr_isApp(v___x_3129_);
                    if v___x_3130_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3129_);
                        crate::leanh::lean_dec(v_a_3107_);
                        crate::leanh::lean_dec(v_goal_3087_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3129_);
                        v___x_3132_ = l_Lean_Expr_isApp(v___x_3131_);
                        if v___x_3132_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3131_);
                            crate::leanh::lean_dec(v_a_3107_);
                            crate::leanh::lean_dec(v_goal_3087_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3131_);
                            v___x_3134_ = l_Lean_Expr_isApp(v___x_3133_);
                            if v___x_3134_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3133_);
                                crate::leanh::lean_dec(v_a_3107_);
                                crate::leanh::lean_dec(v_goal_3087_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3133_);
                                v___x_3136_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__2;
                                v___x_3137_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__3;
                                v___x_3138_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__5;
                                v___x_3139_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__1;
                                v___x_3140_ = l_Lean_Expr_isConstOf(v___x_3135_, v___x_3139_);
                                crate::leanh::lean_dec_ref(v___x_3135_);
                                if v___x_3140_ == 0 {
                                    crate::leanh::lean_dec(v_a_3107_);
                                    crate::leanh::lean_dec(v_goal_3087_);
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_3109_);
                                    v_postCondEntailsRflRule_3141_ =
                                        crate::leanh::lean_ctor_get(v___y_3088_, 8);
                                    v_postCondEntailsMkRule_3142_ =
                                        crate::leanh::lean_ctor_get(v___y_3088_, 9);
                                    v___x_3143_ = crate::leanh::lean_box(0);
                                    crate::leanh::lean_inc(v_goal_3087_);
                                    crate::leanh::lean_inc_ref(v_postCondEntailsRflRule_3141_);
                                    v___x_3144_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_postCondEntailsRflRule_3141_, v_goal_3087_, v___x_3143_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
                                    if crate::leanh::lean_obj_tag(v___x_3144_) == 0 {
                                        v_a_3145_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                                        v_isSharedCheck_3220_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3144_)) as u8;
                                        if v_isSharedCheck_3220_ == 0 {
                                            v___x_3147_ = v___x_3144_;
                                            v_isShared_3148_ = v_isSharedCheck_3220_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3145_);
                                            crate::leanh::lean_dec(v___x_3144_);
                                            v___x_3147_ = crate::leanh::lean_box(0);
                                            v_isShared_3148_ = v_isSharedCheck_3220_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_3107_);
                                        crate::leanh::lean_dec(v_goal_3087_);
                                        v_a_3221_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                                        v_isSharedCheck_3228_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3144_)) as u8;
                                        if v_isSharedCheck_3228_ == 0 {
                                            v___x_3223_ = v___x_3144_;
                                            v_isShared_3224_ = v_isSharedCheck_3228_;
                                            state = 19;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3221_);
                                            crate::leanh::lean_dec(v___x_3144_);
                                            v___x_3223_ = crate::leanh::lean_box(0);
                                            v_isShared_3224_ = v_isSharedCheck_3228_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3112_ = crate::leanh::lean_box(0);
                if v_isShared_3110_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3109_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3114_;
            }
            5 => {
                v___x_3121_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__4);
                v___x_3122_ = l_Lean_MessageData_ofExpr(v_a_3107_);
                v___x_3123_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3123_, 0, v___x_3121_);
                crate::leanh::lean_ctor_set(v___x_3123_, 1, v___x_3122_);
                v___x_3124_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___closed__6);
                v___x_3125_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3125_, 0, v___x_3123_);
                crate::leanh::lean_ctor_set(v___x_3125_, 1, v___x_3124_);
                v___x_3126_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3125_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
                return v___x_3126_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_3145_) == 1 {
                    v_mvarIds_3209_ = crate::leanh::lean_ctor_get(v_a_3145_, 0);
                    v_isSharedCheck_3219_ = (!crate::leanh::lean_is_exclusive(v_a_3145_)) as u8;
                    if v_isSharedCheck_3219_ == 0 {
                        v___x_3211_ = v_a_3145_;
                        v_isShared_3212_ = v_isSharedCheck_3219_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarIds_3209_);
                        crate::leanh::lean_dec(v_a_3145_);
                        v___x_3211_ = crate::leanh::lean_box(0);
                        v_isShared_3212_ = v_isSharedCheck_3219_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3147_);
                    crate::leanh::lean_dec(v_a_3145_);
                    v___y_3150_ = v___y_3088_;
                    v_postCondEntailsMkRule_3151_ = v_postCondEntailsMkRule_3142_;
                    v___y_3152_ = v___y_3089_;
                    v___y_3153_ = v___y_3090_;
                    v___y_3154_ = v___y_3091_;
                    v___y_3155_ = v___y_3092_;
                    v___y_3156_ = v___y_3093_;
                    v___y_3157_ = v___y_3094_;
                    v___y_3158_ = v___y_3095_;
                    v___y_3159_ = v___y_3096_;
                    v___y_3160_ = v___y_3097_;
                    v___y_3161_ = v___y_3098_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v_postCondEntailsMkRule_3151_);
                v___x_3162_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_postCondEntailsMkRule_3151_,
                        v_goal_3087_,
                        v___x_3143_,
                        v___y_3150_,
                        v___y_3152_,
                        v___y_3153_,
                        v___y_3154_,
                        v___y_3155_,
                        v___y_3156_,
                        v___y_3157_,
                        v___y_3158_,
                        v___y_3159_,
                        v___y_3160_,
                        v___y_3161_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3162_) == 0 {
                    v_a_3163_ = crate::leanh::lean_ctor_get(v___x_3162_, 0);
                    crate::leanh::lean_inc(v_a_3163_);
                    crate::leanh::lean_dec_ref_known(v___x_3162_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3163_) == 1 {
                        v_mvarIds_3164_ = crate::leanh::lean_ctor_get(v_a_3163_, 0);
                        crate::leanh::lean_inc(v_mvarIds_3164_);
                        crate::leanh::lean_dec_ref_known(v_a_3163_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_3164_) == 1 {
                            v_tail_3165_ = crate::leanh::lean_ctor_get(v_mvarIds_3164_, 1);
                            crate::leanh::lean_inc(v_tail_3165_);
                            if crate::leanh::lean_obj_tag(v_tail_3165_) == 1 {
                                v_tail_3166_ = crate::leanh::lean_ctor_get(v_tail_3165_, 1);
                                crate::leanh::lean_inc(v_tail_3166_);
                                if crate::leanh::lean_obj_tag(v_tail_3166_) == 0 {
                                    crate::leanh::lean_dec(v_a_3107_);
                                    v_head_3167_ = crate::leanh::lean_ctor_get(v_mvarIds_3164_, 0);
                                    crate::leanh::lean_inc(v_head_3167_);
                                    crate::leanh::lean_dec_ref_known(v_mvarIds_3164_, 2);
                                    v_head_3168_ = crate::leanh::lean_ctor_get(v_tail_3165_, 0);
                                    v_isSharedCheck_3199_ =
                                        (!crate::leanh::lean_is_exclusive(v_tail_3165_)) as u8;
                                    if v_isSharedCheck_3199_ == 0 {
                                        v_unused_3200_ =
                                            crate::leanh::lean_ctor_get(v_tail_3165_, 1);
                                        crate::leanh::lean_dec(v_unused_3200_);
                                        v___x_3170_ = v_tail_3165_;
                                        v_isShared_3171_ = v_isSharedCheck_3199_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_head_3168_);
                                        crate::leanh::lean_dec(v_tail_3165_);
                                        v___x_3170_ = crate::leanh::lean_box(0);
                                        v_isShared_3171_ = v_isSharedCheck_3199_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_tail_3165_, 2);
                                    crate::leanh::lean_dec(v_tail_3166_);
                                    crate::leanh::lean_dec_ref_known(v_mvarIds_3164_, 2);
                                    v___y_3117_ = v___y_3158_;
                                    v___y_3118_ = v___y_3159_;
                                    v___y_3119_ = v___y_3160_;
                                    v___y_3120_ = v___y_3161_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_tail_3165_);
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3164_, 2);
                                v___y_3117_ = v___y_3158_;
                                v___y_3118_ = v___y_3159_;
                                v___y_3119_ = v___y_3160_;
                                v___y_3120_ = v___y_3161_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_3164_);
                            v___y_3117_ = v___y_3158_;
                            v___y_3118_ = v___y_3159_;
                            v___y_3119_ = v___y_3160_;
                            v___y_3120_ = v___y_3161_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3163_);
                        v___y_3117_ = v___y_3158_;
                        v___y_3118_ = v___y_3159_;
                        v___y_3119_ = v___y_3160_;
                        v___y_3120_ = v___y_3161_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3107_);
                    v_a_3201_ = crate::leanh::lean_ctor_get(v___x_3162_, 0);
                    v_isSharedCheck_3208_ = (!crate::leanh::lean_is_exclusive(v___x_3162_)) as u8;
                    if v_isSharedCheck_3208_ == 0 {
                        v___x_3203_ = v___x_3162_;
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3201_);
                        crate::leanh::lean_dec(v___x_3162_);
                        v___x_3203_ = crate::leanh::lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                crate::leanh::lean_inc(v_head_3168_);
                v___x_3172_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_solveExceptCondsEntails___boxed
                        as *mut core::ffi::c_void,
                    13,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3172_, 0, v_head_3168_);
                v___x_3173_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_3168_, v___x_3172_, v___y_3150_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
                if crate::leanh::lean_obj_tag(v___x_3173_) == 0 {
                    v_a_3174_ = crate::leanh::lean_ctor_get(v___x_3173_, 0);
                    crate::leanh::lean_inc(v_a_3174_);
                    crate::leanh::lean_dec_ref_known(v___x_3173_, 1);
                    crate::leanh::lean_inc(v_head_3167_);
                    v___f_3175_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___boxed
                            as *mut core::ffi::c_void,
                        16,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_3175_, 0, v_head_3167_);
                    crate::leanh::lean_closure_set(v___f_3175_, 1, v___x_3136_);
                    crate::leanh::lean_closure_set(v___f_3175_, 2, v___x_3137_);
                    crate::leanh::lean_closure_set(v___f_3175_, 3, v___x_3138_);
                    v___x_3176_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_head_3167_, v___f_3175_, v___y_3150_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
                    if crate::leanh::lean_obj_tag(v___x_3176_) == 0 {
                        if crate::leanh::lean_obj_tag(v_a_3174_) == 0 {
                            crate::leanh::lean_del_object(v___x_3170_);
                            v_a_3177_ = crate::leanh::lean_ctor_get(v___x_3176_, 0);
                            crate::leanh::lean_inc(v_a_3177_);
                            crate::leanh::lean_dec_ref_known(v___x_3176_, 1);
                            v___y_3101_ = v_a_3177_;
                            v___y_3102_ = v_tail_3166_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3178_ = crate::leanh::lean_ctor_get(v___x_3176_, 0);
                            crate::leanh::lean_inc(v_a_3178_);
                            crate::leanh::lean_dec_ref_known(v___x_3176_, 1);
                            v_val_3179_ = crate::leanh::lean_ctor_get(v_a_3174_, 0);
                            crate::leanh::lean_inc(v_val_3179_);
                            crate::leanh::lean_dec_ref_known(v_a_3174_, 1);
                            if v_isShared_3171_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3170_, 0, v_val_3179_);
                                v___x_3181_ = v___x_3170_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_3182_ =
                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_val_3179_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3182_,
                                    1,
                                    v_tail_3166_,
                                );
                                v___x_3181_ = v_reuseFailAlloc_3182_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3174_);
                        crate::leanh::lean_del_object(v___x_3170_);
                        v_a_3183_ = crate::leanh::lean_ctor_get(v___x_3176_, 0);
                        v_isSharedCheck_3190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3176_)) as u8;
                        if v_isSharedCheck_3190_ == 0 {
                            v___x_3185_ = v___x_3176_;
                            v_isShared_3186_ = v_isSharedCheck_3190_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3183_);
                            crate::leanh::lean_dec(v___x_3176_);
                            v___x_3185_ = crate::leanh::lean_box(0);
                            v_isShared_3186_ = v_isSharedCheck_3190_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3170_);
                    crate::leanh::lean_dec(v_head_3167_);
                    v_a_3191_ = crate::leanh::lean_ctor_get(v___x_3173_, 0);
                    v_isSharedCheck_3198_ = (!crate::leanh::lean_is_exclusive(v___x_3173_)) as u8;
                    if v_isSharedCheck_3198_ == 0 {
                        v___x_3193_ = v___x_3173_;
                        v_isShared_3194_ = v_isSharedCheck_3198_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3191_);
                        crate::leanh::lean_dec(v___x_3173_);
                        v___x_3193_ = crate::leanh::lean_box(0);
                        v_isShared_3194_ = v_isSharedCheck_3198_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                v___y_3101_ = v_a_3178_;
                v___y_3102_ = v___x_3181_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_3186_ == 0 {
                    v___x_3188_ = v___x_3185_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
                    v___x_3188_ = v_reuseFailAlloc_3189_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3188_;
            }
            12 => {
                if v_isShared_3194_ == 0 {
                    v___x_3196_ = v___x_3193_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
                    v___x_3196_ = v_reuseFailAlloc_3197_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3196_;
            }
            14 => {
                if v_isShared_3204_ == 0 {
                    v___x_3206_ = v___x_3203_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3206_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_mvarIds_3209_) == 0 {
                    crate::leanh::lean_dec(v_a_3107_);
                    crate::leanh::lean_dec(v_goal_3087_);
                    if v_isShared_3212_ == 0 {
                        v___x_3214_ = v___x_3211_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_mvarIds_3209_);
                        v___x_3214_ = v_reuseFailAlloc_3218_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3211_);
                    crate::leanh::lean_dec(v_mvarIds_3209_);
                    crate::leanh::lean_del_object(v___x_3147_);
                    v___y_3150_ = v___y_3088_;
                    v_postCondEntailsMkRule_3151_ = v_postCondEntailsMkRule_3142_;
                    v___y_3152_ = v___y_3089_;
                    v___y_3153_ = v___y_3090_;
                    v___y_3154_ = v___y_3091_;
                    v___y_3155_ = v___y_3092_;
                    v___y_3156_ = v___y_3093_;
                    v___y_3157_ = v___y_3094_;
                    v___y_3158_ = v___y_3095_;
                    v___y_3159_ = v___y_3096_;
                    v___y_3160_ = v___y_3097_;
                    v___y_3161_ = v___y_3098_;
                    state = 7;
                    continue;
                }
            }
            17 => {
                if v_isShared_3148_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3147_, 0, v___x_3214_);
                    v___x_3216_ = v___x_3147_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
                    v___x_3216_ = v_reuseFailAlloc_3217_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3216_;
            }
            19 => {
                if v_isShared_3224_ == 0 {
                    v___x_3226_ = v___x_3223_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
                    v___x_3226_ = v_reuseFailAlloc_3227_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3226_;
            }
            21 => {
                if v_isShared_3233_ == 0 {
                    v___x_3235_ = v___x_3232_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
                    v___x_3235_ = v_reuseFailAlloc_3236_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___boxed(
    mut v_goal_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3251_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1(
        v_goal_3238_,
        v___y_3239_,
        v___y_3240_,
        v___y_3241_,
        v___y_3242_,
        v___y_3243_,
        v___y_3244_,
        v___y_3245_,
        v___y_3246_,
        v___y_3247_,
        v___y_3248_,
        v___y_3249_,
    );
    crate::leanh::lean_dec(v___y_3249_);
    crate::leanh::lean_dec_ref(v___y_3248_);
    crate::leanh::lean_dec(v___y_3247_);
    crate::leanh::lean_dec_ref(v___y_3246_);
    crate::leanh::lean_dec(v___y_3245_);
    crate::leanh::lean_dec_ref(v___y_3244_);
    crate::leanh::lean_dec(v___y_3243_);
    crate::leanh::lean_dec_ref(v___y_3242_);
    crate::leanh::lean_dec(v___y_3241_);
    crate::leanh::lean_dec(v___y_3240_);
    crate::leanh::lean_dec_ref(v___y_3239_);
    return v_res_3251_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(
    mut v_goal_3252_: *mut crate::leanh::LeanObject,
    mut v_a_3253_: *mut crate::leanh::LeanObject,
    mut v_a_3254_: *mut crate::leanh::LeanObject,
    mut v_a_3255_: *mut crate::leanh::LeanObject,
    mut v_a_3256_: *mut crate::leanh::LeanObject,
    mut v_a_3257_: *mut crate::leanh::LeanObject,
    mut v_a_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_goal_3252_);
    v___f_3265_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__1___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3265_, 0, v_goal_3252_);
    v___x_3266_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_3252_, v___f_3265_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
    return v___x_3266_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___boxed(
    mut v_goal_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
    mut v_a_3271_: *mut crate::leanh::LeanObject,
    mut v_a_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
    mut v_a_3274_: *mut crate::leanh::LeanObject,
    mut v_a_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
    mut v_a_3277_: *mut crate::leanh::LeanObject,
    mut v_a_3278_: *mut crate::leanh::LeanObject,
    mut v_a_3279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3280_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails(
        v_goal_3267_,
        v_a_3268_,
        v_a_3269_,
        v_a_3270_,
        v_a_3271_,
        v_a_3272_,
        v_a_3273_,
        v_a_3274_,
        v_a_3275_,
        v_a_3276_,
        v_a_3277_,
        v_a_3278_,
    );
    crate::leanh::lean_dec(v_a_3278_);
    crate::leanh::lean_dec_ref(v_a_3277_);
    crate::leanh::lean_dec(v_a_3276_);
    crate::leanh::lean_dec_ref(v_a_3275_);
    crate::leanh::lean_dec(v_a_3274_);
    crate::leanh::lean_dec_ref(v_a_3273_);
    crate::leanh::lean_dec(v_a_3272_);
    crate::leanh::lean_dec_ref(v_a_3271_);
    crate::leanh::lean_dec(v_a_3270_);
    crate::leanh::lean_dec(v_a_3269_);
    crate::leanh::lean_dec_ref(v_a_3268_);
    return v_res_3280_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__0;
    v___x_3283_ = l_Lean_stringToMessageData(v___x_3282_);
    return v___x_3283_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ = 0;
    v___x_3291_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__3;
    v___x_3292_ = l_Lean_MessageData_ofConstName(v___x_3291_, v___x_3290_);
    return v___x_3292_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3293_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__4,
    );
    v___x_3294_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1,
    );
    v___x_3295_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3295_, 0, v___x_3294_);
    crate::leanh::lean_ctor_set(v___x_3295_, 1, v___x_3293_);
    return v___x_3295_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(
    mut v_goal_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_goal_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entailsConsIntroRule_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_applyPureConsEntailsLRule_3314_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_applyPureConsEntailsRRule_3315_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3321_: u8 = 0;
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3355_: u8 = 0;
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut v_mvarIds_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3366_: u8 = 0;
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v_a_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3378_: u8 = 0;
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut v_a_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_entailsConsIntroRule_3313_ = crate::leanh::lean_ctor_get(v_a_3297_, 0);
                v_applyPureConsEntailsLRule_3314_ = crate::leanh::lean_ctor_get(v_a_3297_, 3);
                v_applyPureConsEntailsRRule_3315_ = crate::leanh::lean_ctor_get(v_a_3297_, 4);
                v___x_3316_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_entailsConsIntroRule_3313_);
                v___x_3317_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_entailsConsIntroRule_3313_,
                        v_goal_3296_,
                        v___x_3316_,
                        v_a_3297_,
                        v_a_3298_,
                        v_a_3299_,
                        v_a_3300_,
                        v_a_3301_,
                        v_a_3302_,
                        v_a_3303_,
                        v_a_3304_,
                        v_a_3305_,
                        v_a_3306_,
                        v_a_3307_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3317_) == 0 {
                    v_a_3318_ = crate::leanh::lean_ctor_get(v___x_3317_, 0);
                    v_isSharedCheck_3379_ = (!crate::leanh::lean_is_exclusive(v___x_3317_)) as u8;
                    if v_isSharedCheck_3379_ == 0 {
                        v___x_3320_ = v___x_3317_;
                        v_isShared_3321_ = v_isSharedCheck_3379_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3318_);
                        crate::leanh::lean_dec(v___x_3317_);
                        v___x_3320_ = crate::leanh::lean_box(0);
                        v_isShared_3321_ = v_isSharedCheck_3379_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3380_ = crate::leanh::lean_ctor_get(v___x_3317_, 0);
                    v_isSharedCheck_3387_ = (!crate::leanh::lean_is_exclusive(v___x_3317_)) as u8;
                    if v_isSharedCheck_3387_ == 0 {
                        v___x_3382_ = v___x_3317_;
                        v_isShared_3383_ = v_isSharedCheck_3387_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3380_);
                        crate::leanh::lean_dec(v___x_3317_);
                        v___x_3382_ = crate::leanh::lean_box(0);
                        v_isShared_3383_ = v_isSharedCheck_3387_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3311_, 0, v_goal_3310_);
                v___x_3312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3311_);
                return v___x_3312_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3318_) == 1 {
                    v_mvarIds_3326_ = crate::leanh::lean_ctor_get(v_a_3318_, 0);
                    crate::leanh::lean_inc(v_mvarIds_3326_);
                    crate::leanh::lean_dec_ref_known(v_a_3318_, 1);
                    if crate::leanh::lean_obj_tag(v_mvarIds_3326_) == 1 {
                        v_tail_3327_ = crate::leanh::lean_ctor_get(v_mvarIds_3326_, 1);
                        if crate::leanh::lean_obj_tag(v_tail_3327_) == 0 {
                            crate::leanh::lean_del_object(v___x_3320_);
                            v_head_3328_ = crate::leanh::lean_ctor_get(v_mvarIds_3326_, 0);
                            crate::leanh::lean_inc(v_head_3328_);
                            crate::leanh::lean_dec_ref_known(v_mvarIds_3326_, 2);
                            v___x_3329_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__5);
                            v___x_3330_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
                                v_head_3328_,
                                v___x_3329_,
                                v_a_3297_,
                                v_a_3298_,
                                v_a_3302_,
                                v_a_3303_,
                                v_a_3304_,
                                v_a_3305_,
                                v_a_3306_,
                                v_a_3307_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3330_) == 0 {
                                v_a_3331_ = crate::leanh::lean_ctor_get(v___x_3330_, 0);
                                crate::leanh::lean_inc_n(v_a_3331_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_3330_, 1);
                                crate::leanh::lean_inc_ref(v_applyPureConsEntailsLRule_3314_);
                                v___x_3332_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_applyPureConsEntailsLRule_3314_, v_a_3331_, v___x_3316_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_);
                                if crate::leanh::lean_obj_tag(v___x_3332_) == 0 {
                                    v_a_3333_ = crate::leanh::lean_ctor_get(v___x_3332_, 0);
                                    crate::leanh::lean_inc(v_a_3333_);
                                    crate::leanh::lean_dec_ref_known(v___x_3332_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_3333_) == 1 {
                                        v_mvarIds_3360_ = crate::leanh::lean_ctor_get(v_a_3333_, 0);
                                        crate::leanh::lean_inc(v_mvarIds_3360_);
                                        crate::leanh::lean_dec_ref_known(v_a_3333_, 1);
                                        if crate::leanh::lean_obj_tag(v_mvarIds_3360_) == 1 {
                                            v_tail_3361_ =
                                                crate::leanh::lean_ctor_get(v_mvarIds_3360_, 1);
                                            if crate::leanh::lean_obj_tag(v_tail_3361_) == 0 {
                                                crate::leanh::lean_dec(v_a_3331_);
                                                v_head_3362_ =
                                                    crate::leanh::lean_ctor_get(v_mvarIds_3360_, 0);
                                                crate::leanh::lean_inc(v_head_3362_);
                                                crate::leanh::lean_dec_ref_known(
                                                    v_mvarIds_3360_,
                                                    2,
                                                );
                                                v_goal_3335_ = v_head_3362_;
                                                v___y_3336_ = v_a_3297_;
                                                v___y_3337_ = v_a_3298_;
                                                v___y_3338_ = v_a_3299_;
                                                v___y_3339_ = v_a_3300_;
                                                v___y_3340_ = v_a_3301_;
                                                v___y_3341_ = v_a_3302_;
                                                v___y_3342_ = v_a_3303_;
                                                v___y_3343_ = v_a_3304_;
                                                v___y_3344_ = v_a_3305_;
                                                v___y_3345_ = v_a_3306_;
                                                v___y_3346_ = v_a_3307_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(
                                                    v_mvarIds_3360_,
                                                    2,
                                                );
                                                v_goal_3335_ = v_a_3331_;
                                                v___y_3336_ = v_a_3297_;
                                                v___y_3337_ = v_a_3298_;
                                                v___y_3338_ = v_a_3299_;
                                                v___y_3339_ = v_a_3300_;
                                                v___y_3340_ = v_a_3301_;
                                                v___y_3341_ = v_a_3302_;
                                                v___y_3342_ = v_a_3303_;
                                                v___y_3343_ = v_a_3304_;
                                                v___y_3344_ = v_a_3305_;
                                                v___y_3345_ = v_a_3306_;
                                                v___y_3346_ = v_a_3307_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_mvarIds_3360_);
                                            v_goal_3335_ = v_a_3331_;
                                            v___y_3336_ = v_a_3297_;
                                            v___y_3337_ = v_a_3298_;
                                            v___y_3338_ = v_a_3299_;
                                            v___y_3339_ = v_a_3300_;
                                            v___y_3340_ = v_a_3301_;
                                            v___y_3341_ = v_a_3302_;
                                            v___y_3342_ = v_a_3303_;
                                            v___y_3343_ = v_a_3304_;
                                            v___y_3344_ = v_a_3305_;
                                            v___y_3345_ = v_a_3306_;
                                            v___y_3346_ = v_a_3307_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_3333_);
                                        v_goal_3335_ = v_a_3331_;
                                        v___y_3336_ = v_a_3297_;
                                        v___y_3337_ = v_a_3298_;
                                        v___y_3338_ = v_a_3299_;
                                        v___y_3339_ = v_a_3300_;
                                        v___y_3340_ = v_a_3301_;
                                        v___y_3341_ = v_a_3302_;
                                        v___y_3342_ = v_a_3303_;
                                        v___y_3343_ = v_a_3304_;
                                        v___y_3344_ = v_a_3305_;
                                        v___y_3345_ = v_a_3306_;
                                        v___y_3346_ = v_a_3307_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3331_);
                                    v_a_3363_ = crate::leanh::lean_ctor_get(v___x_3332_, 0);
                                    v_isSharedCheck_3370_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3332_)) as u8;
                                    if v_isSharedCheck_3370_ == 0 {
                                        v___x_3365_ = v___x_3332_;
                                        v_isShared_3366_ = v_isSharedCheck_3370_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3363_);
                                        crate::leanh::lean_dec(v___x_3332_);
                                        v___x_3365_ = crate::leanh::lean_box(0);
                                        v_isShared_3366_ = v_isSharedCheck_3370_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_3371_ = crate::leanh::lean_ctor_get(v___x_3330_, 0);
                                v_isSharedCheck_3378_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3330_)) as u8;
                                if v_isSharedCheck_3378_ == 0 {
                                    v___x_3373_ = v___x_3330_;
                                    v_isShared_3374_ = v_isSharedCheck_3378_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3371_);
                                    crate::leanh::lean_dec(v___x_3330_);
                                    v___x_3373_ = crate::leanh::lean_box(0);
                                    v_isShared_3374_ = v_isSharedCheck_3378_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_mvarIds_3326_, 2);
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarIds_3326_);
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3318_);
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3316_);
                    v___x_3324_ = v___x_3320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3316_);
                    v___x_3324_ = v_reuseFailAlloc_3325_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3324_;
            }
            5 => {
                crate::leanh::lean_inc(v_goal_3335_);
                crate::leanh::lean_inc_ref(v_applyPureConsEntailsRRule_3315_);
                v___x_3347_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_applyPureConsEntailsRRule_3315_,
                        v_goal_3335_,
                        v___x_3316_,
                        v___y_3336_,
                        v___y_3337_,
                        v___y_3338_,
                        v___y_3339_,
                        v___y_3340_,
                        v___y_3341_,
                        v___y_3342_,
                        v___y_3343_,
                        v___y_3344_,
                        v___y_3345_,
                        v___y_3346_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3347_) == 0 {
                    v_a_3348_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                    crate::leanh::lean_inc(v_a_3348_);
                    crate::leanh::lean_dec_ref_known(v___x_3347_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3348_) == 1 {
                        v_mvarIds_3349_ = crate::leanh::lean_ctor_get(v_a_3348_, 0);
                        crate::leanh::lean_inc(v_mvarIds_3349_);
                        crate::leanh::lean_dec_ref_known(v_a_3348_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_3349_) == 1 {
                            v_tail_3350_ = crate::leanh::lean_ctor_get(v_mvarIds_3349_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_3350_) == 0 {
                                crate::leanh::lean_dec(v_goal_3335_);
                                v_head_3351_ = crate::leanh::lean_ctor_get(v_mvarIds_3349_, 0);
                                crate::leanh::lean_inc(v_head_3351_);
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3349_, 2);
                                v_goal_3310_ = v_head_3351_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3349_, 2);
                                v_goal_3310_ = v_goal_3335_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_3349_);
                            v_goal_3310_ = v_goal_3335_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3348_);
                        v_goal_3310_ = v_goal_3335_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_3335_);
                    v_a_3352_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                    v_isSharedCheck_3359_ = (!crate::leanh::lean_is_exclusive(v___x_3347_)) as u8;
                    if v_isSharedCheck_3359_ == 0 {
                        v___x_3354_ = v___x_3347_;
                        v_isShared_3355_ = v_isSharedCheck_3359_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3352_);
                        crate::leanh::lean_dec(v___x_3347_);
                        v___x_3354_ = crate::leanh::lean_box(0);
                        v_isShared_3355_ = v_isSharedCheck_3359_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3355_ == 0 {
                    v___x_3357_ = v___x_3354_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3358_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
                    v___x_3357_ = v_reuseFailAlloc_3358_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3357_;
            }
            8 => {
                if v_isShared_3366_ == 0 {
                    v___x_3368_ = v___x_3365_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
                    v___x_3368_ = v_reuseFailAlloc_3369_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3368_;
            }
            10 => {
                if v_isShared_3374_ == 0 {
                    v___x_3376_ = v___x_3373_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
                    v___x_3376_ = v_reuseFailAlloc_3377_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3376_;
            }
            12 => {
                if v_isShared_3383_ == 0 {
                    v___x_3385_ = v___x_3382_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
                    v___x_3385_ = v_reuseFailAlloc_3386_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___boxed(
    mut v_goal_3388_: *mut crate::leanh::LeanObject,
    mut v_a_3389_: *mut crate::leanh::LeanObject,
    mut v_a_3390_: *mut crate::leanh::LeanObject,
    mut v_a_3391_: *mut crate::leanh::LeanObject,
    mut v_a_3392_: *mut crate::leanh::LeanObject,
    mut v_a_3393_: *mut crate::leanh::LeanObject,
    mut v_a_3394_: *mut crate::leanh::LeanObject,
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
    mut v_a_3397_: *mut crate::leanh::LeanObject,
    mut v_a_3398_: *mut crate::leanh::LeanObject,
    mut v_a_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(
        v_goal_3388_,
        v_a_3389_,
        v_a_3390_,
        v_a_3391_,
        v_a_3392_,
        v_a_3393_,
        v_a_3394_,
        v_a_3395_,
        v_a_3396_,
        v_a_3397_,
        v_a_3398_,
        v_a_3399_,
    );
    crate::leanh::lean_dec(v_a_3399_);
    crate::leanh::lean_dec_ref(v_a_3398_);
    crate::leanh::lean_dec(v_a_3397_);
    crate::leanh::lean_dec_ref(v_a_3396_);
    crate::leanh::lean_dec(v_a_3395_);
    crate::leanh::lean_dec_ref(v_a_3394_);
    crate::leanh::lean_dec(v_a_3393_);
    crate::leanh::lean_dec_ref(v_a_3392_);
    crate::leanh::lean_dec(v_a_3391_);
    crate::leanh::lean_dec(v_a_3390_);
    crate::leanh::lean_dec_ref(v_a_3389_);
    return v_res_3401_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__0;
    v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
    return v___x_3404_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3406_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__2;
    v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
    return v___x_3407_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__4;
    v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
    return v___x_3410_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(
    mut v_a_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
    mut v___y_3419_: *mut crate::leanh::LeanObject,
    mut v___y_3420_: *mut crate::leanh::LeanObject,
    mut v___y_3421_: *mut crate::leanh::LeanObject,
    mut v___y_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut v_a_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3424_ = crate::leanh::lean_ctor_get(v_a_3411_, 0);
                v_snd_3425_ = crate::leanh::lean_ctor_get(v_a_3411_, 1);
                v_isSharedCheck_3477_ = (!crate::leanh::lean_is_exclusive(v_a_3411_)) as u8;
                if v_isSharedCheck_3477_ == 0 {
                    v___x_3427_ = v_a_3411_;
                    v_isShared_3428_ = v_isSharedCheck_3477_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3425_);
                    crate::leanh::lean_inc(v_fst_3424_);
                    crate::leanh::lean_dec(v_a_3411_);
                    v___x_3427_ = crate::leanh::lean_box(0);
                    v_isShared_3428_ = v_isSharedCheck_3477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3429_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3430_ = lean_nat_dec_lt(v___x_3429_, v_fst_3424_);
                if v___x_3430_ == 0 {
                    if v_isShared_3428_ == 0 {
                        v___x_3432_ = v___x_3427_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_fst_3424_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_snd_3425_);
                        v___x_3432_ = v_reuseFailAlloc_3434_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_snd_3425_);
                    v___x_3435_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(
                        v_snd_3425_,
                        v___y_3412_,
                        v___y_3413_,
                        v___y_3414_,
                        v___y_3415_,
                        v___y_3416_,
                        v___y_3417_,
                        v___y_3418_,
                        v___y_3419_,
                        v___y_3420_,
                        v___y_3421_,
                        v___y_3422_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3435_) == 0 {
                        v_a_3436_ = crate::leanh::lean_ctor_get(v___x_3435_, 0);
                        crate::leanh::lean_inc(v_a_3436_);
                        crate::leanh::lean_dec_ref_known(v___x_3435_, 1);
                        v___x_3437_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3438_ = lean_nat_sub(v_fst_3424_, v___x_3437_);
                        crate::leanh::lean_dec(v_fst_3424_);
                        if crate::leanh::lean_obj_tag(v_a_3436_) == 1 {
                            crate::leanh::lean_dec(v_snd_3425_);
                            v_val_3439_ = crate::leanh::lean_ctor_get(v_a_3436_, 0);
                            crate::leanh::lean_inc(v_val_3439_);
                            crate::leanh::lean_dec_ref_known(v_a_3436_, 1);
                            if v_isShared_3428_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3427_, 1, v_val_3439_);
                                crate::leanh::lean_ctor_set(v___x_3427_, 0, v___x_3438_);
                                v___x_3441_ = v___x_3427_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3443_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3438_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 1, v_val_3439_);
                                v___x_3441_ = v_reuseFailAlloc_3443_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3436_);
                            v___x_3444_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__1);
                            crate::leanh::lean_inc(v_snd_3425_);
                            v___x_3445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3445_, 0, v_snd_3425_);
                            v___x_3446_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3446_, 0, v___x_3444_);
                            crate::leanh::lean_ctor_set(v___x_3446_, 1, v___x_3445_);
                            v___x_3447_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__3);
                            v___x_3448_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3448_, 0, v___x_3446_);
                            crate::leanh::lean_ctor_set(v___x_3448_, 1, v___x_3447_);
                            v___x_3449_ = lean_nat_add(v___x_3438_, v___x_3437_);
                            v___x_3450_ = l_Nat_reprFast(v___x_3449_);
                            v___x_3451_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3451_, 0, v___x_3450_);
                            v___x_3452_ = l_Lean_MessageData_ofFormat(v___x_3451_);
                            v___x_3453_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3453_, 0, v___x_3448_);
                            crate::leanh::lean_ctor_set(v___x_3453_, 1, v___x_3452_);
                            v___x_3454_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___closed__5);
                            v___x_3455_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3455_, 0, v___x_3453_);
                            crate::leanh::lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                            v___x_3456_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3455_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
                            if crate::leanh::lean_obj_tag(v___x_3456_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3456_, 1);
                                if v_isShared_3428_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3427_, 0, v___x_3438_);
                                    v___x_3458_ = v___x_3427_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3460_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3460_,
                                        0,
                                        v___x_3438_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3460_,
                                        1,
                                        v_snd_3425_,
                                    );
                                    v___x_3458_ = v_reuseFailAlloc_3460_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_3438_);
                                crate::leanh::lean_del_object(v___x_3427_);
                                crate::leanh::lean_dec(v_snd_3425_);
                                v_a_3461_ = crate::leanh::lean_ctor_get(v___x_3456_, 0);
                                v_isSharedCheck_3468_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3456_)) as u8;
                                if v_isSharedCheck_3468_ == 0 {
                                    v___x_3463_ = v___x_3456_;
                                    v_isShared_3464_ = v_isSharedCheck_3468_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3461_);
                                    crate::leanh::lean_dec(v___x_3456_);
                                    v___x_3463_ = crate::leanh::lean_box(0);
                                    v_isShared_3464_ = v_isSharedCheck_3468_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3427_);
                        crate::leanh::lean_dec(v_snd_3425_);
                        crate::leanh::lean_dec(v_fst_3424_);
                        v_a_3469_ = crate::leanh::lean_ctor_get(v___x_3435_, 0);
                        v_isSharedCheck_3476_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3435_)) as u8;
                        if v_isSharedCheck_3476_ == 0 {
                            v___x_3471_ = v___x_3435_;
                            v_isShared_3472_ = v_isSharedCheck_3476_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3469_);
                            crate::leanh::lean_dec(v___x_3435_);
                            v___x_3471_ = crate::leanh::lean_box(0);
                            v_isShared_3472_ = v_isSharedCheck_3476_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                return v___x_3433_;
            }
            3 => {
                v_a_3411_ = v___x_3441_;
                state = 0;
                continue;
            }
            4 => {
                v_a_3411_ = v___x_3458_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3464_ == 0 {
                    v___x_3466_ = v___x_3463_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
                    v___x_3466_ = v_reuseFailAlloc_3467_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3466_;
            }
            7 => {
                if v_isShared_3472_ == 0 {
                    v___x_3474_ = v___x_3471_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
                    v___x_3474_ = v_reuseFailAlloc_3475_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg___boxed(
    mut v_a_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v___y_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3491_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v_a_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
    crate::leanh::lean_dec(v___y_3489_);
    crate::leanh::lean_dec_ref(v___y_3488_);
    crate::leanh::lean_dec(v___y_3487_);
    crate::leanh::lean_dec_ref(v___y_3486_);
    crate::leanh::lean_dec(v___y_3485_);
    crate::leanh::lean_dec_ref(v___y_3484_);
    crate::leanh::lean_dec(v___y_3483_);
    crate::leanh::lean_dec_ref(v___y_3482_);
    crate::leanh::lean_dec(v___y_3481_);
    crate::leanh::lean_dec(v___y_3480_);
    crate::leanh::lean_dec_ref(v___y_3479_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(
    mut v_thm_3492_: *mut crate::leanh::LeanObject,
    mut v_goal_3493_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
    mut v_a_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_a_3500_: *mut crate::leanh::LeanObject,
    mut v_a_3501_: *mut crate::leanh::LeanObject,
    mut v_a_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v_a_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_etaPotential_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v_snd_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_a_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_3507_ = crate::leanh::lean_ctor_get(v_thm_3492_, 2);
                crate::leanh::lean_inc_ref(v_kind_3507_);
                crate::leanh::lean_dec_ref(v_thm_3492_);
                if crate::leanh::lean_obj_tag(v_kind_3507_) == 0 {
                    v_etaPotential_3508_ = crate::leanh::lean_ctor_get(v_kind_3507_, 0);
                    v_isSharedCheck_3542_ = (!crate::leanh::lean_is_exclusive(v_kind_3507_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3510_ = v_kind_3507_;
                        v_isShared_3511_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_etaPotential_3508_);
                        crate::leanh::lean_dec(v_kind_3507_);
                        v___x_3510_ = crate::leanh::lean_box(0);
                        v_isShared_3511_ = v_isSharedCheck_3542_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kind_3507_);
                    crate::leanh::lean_dec(v_goal_3493_);
                    v___x_3543_ = crate::leanh::lean_box(0);
                    v___x_3544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                    return v___x_3544_;
                }
            }
            1 => {
                v___x_3512_ = lean_array_get_size(v_excessArgs_3494_);
                v_n_3513_ = lean_nat_sub(v_etaPotential_3508_, v___x_3512_);
                crate::leanh::lean_dec(v_etaPotential_3508_);
                v___x_3514_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3515_ = lean_nat_dec_eq(v_n_3513_, v___x_3514_);
                if v___x_3515_ == 0 {
                    v___x_3516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3516_, 0, v_n_3513_);
                    crate::leanh::lean_ctor_set(v___x_3516_, 1, v_goal_3493_);
                    v___x_3517_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v___x_3516_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
                    if crate::leanh::lean_obj_tag(v___x_3517_) == 0 {
                        v_a_3518_ = crate::leanh::lean_ctor_get(v___x_3517_, 0);
                        v_isSharedCheck_3529_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3517_)) as u8;
                        if v_isSharedCheck_3529_ == 0 {
                            v___x_3520_ = v___x_3517_;
                            v_isShared_3521_ = v_isSharedCheck_3529_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3518_);
                            crate::leanh::lean_dec(v___x_3517_);
                            v___x_3520_ = crate::leanh::lean_box(0);
                            v_isShared_3521_ = v_isSharedCheck_3529_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3510_);
                        v_a_3530_ = crate::leanh::lean_ctor_get(v___x_3517_, 0);
                        v_isSharedCheck_3537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3517_)) as u8;
                        if v_isSharedCheck_3537_ == 0 {
                            v___x_3532_ = v___x_3517_;
                            v_isShared_3533_ = v_isSharedCheck_3537_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3530_);
                            crate::leanh::lean_dec(v___x_3517_);
                            v___x_3532_ = crate::leanh::lean_box(0);
                            v_isShared_3533_ = v_isSharedCheck_3537_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_n_3513_);
                    crate::leanh::lean_dec(v_goal_3493_);
                    v___x_3538_ = crate::leanh::lean_box(0);
                    if v_isShared_3511_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3510_, 0, v___x_3538_);
                        v___x_3540_ = v___x_3510_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3541_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
                        v___x_3540_ = v_reuseFailAlloc_3541_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_3522_ = crate::leanh::lean_ctor_get(v_a_3518_, 1);
                crate::leanh::lean_inc(v_snd_3522_);
                crate::leanh::lean_dec(v_a_3518_);
                if v_isShared_3511_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3510_, 1);
                    crate::leanh::lean_ctor_set(v___x_3510_, 0, v_snd_3522_);
                    v___x_3524_ = v___x_3510_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_snd_3522_);
                    v___x_3524_ = v_reuseFailAlloc_3528_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3521_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3520_, 0, v___x_3524_);
                    v___x_3526_ = v___x_3520_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3526_;
            }
            5 => {
                if v_isShared_3533_ == 0 {
                    v___x_3535_ = v___x_3532_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
                    v___x_3535_ = v_reuseFailAlloc_3536_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3535_;
            }
            7 => {
                return v___x_3540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro___boxed(
    mut v_thm_3545_: *mut crate::leanh::LeanObject,
    mut v_goal_3546_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3560_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro(
        v_thm_3545_,
        v_goal_3546_,
        v_excessArgs_3547_,
        v_a_3548_,
        v_a_3549_,
        v_a_3550_,
        v_a_3551_,
        v_a_3552_,
        v_a_3553_,
        v_a_3554_,
        v_a_3555_,
        v_a_3556_,
        v_a_3557_,
        v_a_3558_,
    );
    crate::leanh::lean_dec(v_a_3558_);
    crate::leanh::lean_dec_ref(v_a_3557_);
    crate::leanh::lean_dec(v_a_3556_);
    crate::leanh::lean_dec_ref(v_a_3555_);
    crate::leanh::lean_dec(v_a_3554_);
    crate::leanh::lean_dec_ref(v_a_3553_);
    crate::leanh::lean_dec(v_a_3552_);
    crate::leanh::lean_dec_ref(v_a_3551_);
    crate::leanh::lean_dec(v_a_3550_);
    crate::leanh::lean_dec(v_a_3549_);
    crate::leanh::lean_dec_ref(v_a_3548_);
    crate::leanh::lean_dec_ref(v_excessArgs_3547_);
    return v_res_3560_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0(
    mut v_inst_3561_: *mut crate::leanh::LeanObject,
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
    mut v___y_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
    mut v___y_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
    mut v___y_3569_: *mut crate::leanh::LeanObject,
    mut v___y_3570_: *mut crate::leanh::LeanObject,
    mut v___y_3571_: *mut crate::leanh::LeanObject,
    mut v___y_3572_: *mut crate::leanh::LeanObject,
    mut v___y_3573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3575_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___redArg(v_a_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
    return v___x_3575_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0___boxed(
    mut v_inst_3576_: *mut crate::leanh::LeanObject,
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
    mut v___y_3585_: *mut crate::leanh::LeanObject,
    mut v___y_3586_: *mut crate::leanh::LeanObject,
    mut v___y_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3590_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_neededStateIntro_spec__0(v_inst_3576_, v_a_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
    crate::leanh::lean_dec(v___y_3588_);
    crate::leanh::lean_dec_ref(v___y_3587_);
    crate::leanh::lean_dec(v___y_3586_);
    crate::leanh::lean_dec_ref(v___y_3585_);
    crate::leanh::lean_dec(v___y_3584_);
    crate::leanh::lean_dec_ref(v___y_3583_);
    crate::leanh::lean_dec(v___y_3582_);
    crate::leanh::lean_dec_ref(v___y_3581_);
    crate::leanh::lean_dec(v___y_3580_);
    crate::leanh::lean_dec(v___y_3579_);
    crate::leanh::lean_dec_ref(v___y_3578_);
    return v_res_3590_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(
    mut v_progress_3591_: u8,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
    mut v___y_3597_: *mut crate::leanh::LeanObject,
    mut v___y_3598_: *mut crate::leanh::LeanObject,
    mut v___y_3599_: *mut crate::leanh::LeanObject,
    mut v___y_3600_: *mut crate::leanh::LeanObject,
    mut v___y_3601_: *mut crate::leanh::LeanObject,
    mut v___y_3602_: *mut crate::leanh::LeanObject,
    mut v___y_3603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3609_: u8 = 0;
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v_val_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut v_a_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3631_: u8 = 0;
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v_isSharedCheck_3636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3605_ = crate::leanh::lean_ctor_get(v_a_3592_, 0);
                v_snd_3606_ = crate::leanh::lean_ctor_get(v_a_3592_, 1);
                v_isSharedCheck_3636_ = (!crate::leanh::lean_is_exclusive(v_a_3592_)) as u8;
                if v_isSharedCheck_3636_ == 0 {
                    v___x_3608_ = v_a_3592_;
                    v_isShared_3609_ = v_isSharedCheck_3636_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3606_);
                    crate::leanh::lean_inc(v_fst_3605_);
                    crate::leanh::lean_dec(v_a_3592_);
                    v___x_3608_ = crate::leanh::lean_box(0);
                    v_isShared_3609_ = v_isSharedCheck_3636_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_snd_3606_);
                v___x_3610_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep(
                    v_snd_3606_,
                    v___y_3593_,
                    v___y_3594_,
                    v___y_3595_,
                    v___y_3596_,
                    v___y_3597_,
                    v___y_3598_,
                    v___y_3599_,
                    v___y_3600_,
                    v___y_3601_,
                    v___y_3602_,
                    v___y_3603_,
                );
                if crate::leanh::lean_obj_tag(v___x_3610_) == 0 {
                    v_a_3611_ = crate::leanh::lean_ctor_get(v___x_3610_, 0);
                    v_isSharedCheck_3627_ = (!crate::leanh::lean_is_exclusive(v___x_3610_)) as u8;
                    if v_isSharedCheck_3627_ == 0 {
                        v___x_3613_ = v___x_3610_;
                        v_isShared_3614_ = v_isSharedCheck_3627_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3611_);
                        crate::leanh::lean_dec(v___x_3610_);
                        v___x_3613_ = crate::leanh::lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3627_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3608_);
                    crate::leanh::lean_dec(v_snd_3606_);
                    crate::leanh::lean_dec(v_fst_3605_);
                    v_a_3628_ = crate::leanh::lean_ctor_get(v___x_3610_, 0);
                    v_isSharedCheck_3635_ = (!crate::leanh::lean_is_exclusive(v___x_3610_)) as u8;
                    if v_isSharedCheck_3635_ == 0 {
                        v___x_3630_ = v___x_3610_;
                        v_isShared_3631_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3628_);
                        crate::leanh::lean_dec(v___x_3610_);
                        v___x_3630_ = crate::leanh::lean_box(0);
                        v_isShared_3631_ = v_isSharedCheck_3635_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3611_) == 1 {
                    crate::leanh::lean_del_object(v___x_3613_);
                    crate::leanh::lean_dec(v_snd_3606_);
                    crate::leanh::lean_dec(v_fst_3605_);
                    v_val_3615_ = crate::leanh::lean_ctor_get(v_a_3611_, 0);
                    crate::leanh::lean_inc(v_val_3615_);
                    crate::leanh::lean_dec_ref_known(v_a_3611_, 1);
                    v___x_3616_ = crate::leanh::lean_box((v_progress_3591_) as usize);
                    if v_isShared_3609_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3608_, 1, v_val_3615_);
                        crate::leanh::lean_ctor_set(v___x_3608_, 0, v___x_3616_);
                        v___x_3618_ = v___x_3608_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3620_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3616_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_val_3615_);
                        v___x_3618_ = v_reuseFailAlloc_3620_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3611_);
                    if v_isShared_3609_ == 0 {
                        v___x_3622_ = v___x_3608_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_fst_3605_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_snd_3606_);
                        v___x_3622_ = v_reuseFailAlloc_3626_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_3592_ = v___x_3618_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3614_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3622_);
                    v___x_3624_ = v___x_3613_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
                    v___x_3624_ = v_reuseFailAlloc_3625_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3624_;
            }
            6 => {
                if v_isShared_3631_ == 0 {
                    v___x_3633_ = v___x_3630_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
                    v___x_3633_ = v_reuseFailAlloc_3634_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg___boxed(
    mut v_progress_3637_: *mut crate::leanh::LeanObject,
    mut v_a_3638_: *mut crate::leanh::LeanObject,
    mut v___y_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
    mut v___y_3648_: *mut crate::leanh::LeanObject,
    mut v___y_3649_: *mut crate::leanh::LeanObject,
    mut v___y_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_progress_boxed_3651_: u8 = 0;
    let mut v_res_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_progress_boxed_3651_ = (crate::leanh::lean_unbox(v_progress_3637_) as u8);
    v_res_3652_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_boxed_3651_, v_a_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
    crate::leanh::lean_dec(v___y_3649_);
    crate::leanh::lean_dec_ref(v___y_3648_);
    crate::leanh::lean_dec(v___y_3647_);
    crate::leanh::lean_dec_ref(v___y_3646_);
    crate::leanh::lean_dec(v___y_3645_);
    crate::leanh::lean_dec_ref(v___y_3644_);
    crate::leanh::lean_dec(v___y_3643_);
    crate::leanh::lean_dec_ref(v___y_3642_);
    crate::leanh::lean_dec(v___y_3641_);
    crate::leanh::lean_dec(v___y_3640_);
    crate::leanh::lean_dec_ref(v___y_3639_);
    return v_res_3652_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_progress_3659_: u8 = 0;
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_progress_3659_ = 0;
    v___x_3660_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__1;
    v___x_3661_ = l_Lean_MessageData_ofConstName(v___x_3660_, v_progress_3659_);
    return v___x_3661_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2,
    );
    v___x_3663_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1,
    );
    v___x_3664_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3664_, 0, v___x_3663_);
    crate::leanh::lean_ctor_set(v___x_3664_, 1, v___x_3662_);
    return v___x_3664_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v_progress_3677_: u8 = 0;
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_progress_3677_ = 0;
    v___x_3678_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__7;
    v___x_3679_ = l_Lean_MessageData_ofConstName(v___x_3678_, v_progress_3677_);
    return v___x_3679_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3680_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__8,
    );
    v___x_3681_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_consIntroAndSimpStep___closed__1,
    );
    v___x_3682_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3682_, 0, v___x_3681_);
    crate::leanh::lean_ctor_set(v___x_3682_, 1, v___x_3680_);
    return v___x_3682_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3685_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__11;
    v___x_3686_ = l_Lean_stringToMessageData(v___x_3685_);
    return v___x_3686_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v_progress_3693_: u8 = 0;
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_progress_3693_ = 0;
    v___x_3694_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__14;
    v___x_3695_ = l_Lean_MessageData_ofConstName(v___x_3694_, v_progress_3693_);
    return v___x_3695_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3696_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__15,
    );
    v___x_3697_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12,
    );
    v___x_3698_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3698_, 0, v___x_3697_);
    crate::leanh::lean_ctor_set(v___x_3698_, 1, v___x_3696_);
    return v___x_3698_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3699_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_3700_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__16,
    );
    v___x_3701_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3701_, 0, v___x_3700_);
    crate::leanh::lean_ctor_set(v___x_3701_, 1, v___x_3699_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__2,
    );
    v___x_3703_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__12,
    );
    v___x_3704_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3704_, 0, v___x_3703_);
    crate::leanh::lean_ctor_set(v___x_3704_, 1, v___x_3702_);
    return v___x_3704_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3705_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__1___closed__8,
    );
    v___x_3706_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18_once
        ),
        _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__18,
    );
    v___x_3707_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3707_, 0, v___x_3706_);
    crate::leanh::lean_ctor_set(v___x_3707_, 1, v___x_3705_);
    return v___x_3707_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3710_ = crate::leanh::lean_box(0);
    v___x_3711_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__20;
    v___x_3712_ = l_Lean_mkConst(v___x_3711_, v___x_3710_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0(
    mut v_goal_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_progress_3729_: u8 = 0;
    let mut v_goal_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: u8 = 0;
    let mut v_progress_3737_: u8 = 0;
    let mut v_goal_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_downPureIntroRule_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3760_: u8 = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3764_: u8 = 0;
    let mut v___y_3766_: u8 = 0;
    let mut v_progress_3767_: u8 = 0;
    let mut v_goal_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_downPureIntroRule_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureIntroRule_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v___y_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3820_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v_arg_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: u8 = 0;
    let mut v_arg_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_progress_3836_: u8 = 0;
    let mut v_progress_3837_: u8 = 0;
    let mut v___y_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: u8 = 0;
    let mut v_downPureIntroRule_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureElimRule_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureIntroRule_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3868_: u8 = 0;
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3872_: u8 = 0;
    let mut v___x_3873_: u8 = 0;
    let mut v___x_3874_: u8 = 0;
    let mut v___x_3875_: u8 = 0;
    let mut v_a_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3883_: u8 = 0;
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_progress_3887_: u8 = 0;
    let mut v___y_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: u8 = 0;
    let mut v_arg_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: u8 = 0;
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v_entailsNilIntroRule_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_downPureIntroRule_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3932_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v___x_3937_: u8 = 0;
    let mut v___x_3938_: u8 = 0;
    let mut v___x_3939_: u8 = 0;
    let mut v_a_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3947_: u8 = 0;
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v_downPureIntroRule_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureIntroRule_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v_a_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3960_: u8 = 0;
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3964_: u8 = 0;
    let mut v_a_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v___y_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3975_: u8 = 0;
    let mut v___y_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_a_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4008_: u8 = 0;
    let mut v___y_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_progress_4011_: u8 = 0;
    let mut v_goal_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v_pureIntroRule_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4033_: u8 = 0;
    let mut v_mvarIds_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v_a_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4051_: u8 = 0;
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_unused_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_progress_4057_: u8 = 0;
    let mut v_goal_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4093_: u8 = 0;
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_a_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4105_: u8 = 0;
    let mut v___y_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureHNonTrue_4109_: u8 = 0;
    let mut v___y_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pureElimRule_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4134_: u8 = 0;
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut v_a_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4146_: u8 = 0;
    let mut v___y_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: u8 = 0;
    let mut v_a_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v_a_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4161_: u8 = 0;
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v___y_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: u8 = 0;
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: u8 = 0;
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4178_: u8 = 0;
    let mut v_a_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4182_: u8 = 0;
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_3715_);
                v___x_3816_ = l_Lean_MVarId_getType(
                    v_goal_3715_,
                    v___y_3723_,
                    v___y_3724_,
                    v___y_3725_,
                    v___y_3726_,
                );
                if crate::leanh::lean_obj_tag(v___x_3816_) == 0 {
                    v_a_3817_ = crate::leanh::lean_ctor_get(v___x_3816_, 0);
                    v_isSharedCheck_4178_ = (!crate::leanh::lean_is_exclusive(v___x_3816_)) as u8;
                    if v_isSharedCheck_4178_ == 0 {
                        v___x_3819_ = v___x_3816_;
                        v_isShared_3820_ = v_isSharedCheck_4178_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3817_);
                        crate::leanh::lean_dec(v___x_3816_);
                        v___x_3819_ = crate::leanh::lean_box(0);
                        v_isShared_3820_ = v_isSharedCheck_4178_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_3715_);
                    v_a_4179_ = crate::leanh::lean_ctor_get(v___x_3816_, 0);
                    v_isSharedCheck_4186_ = (!crate::leanh::lean_is_exclusive(v___x_3816_)) as u8;
                    if v_isSharedCheck_4186_ == 0 {
                        v___x_4181_ = v___x_3816_;
                        v_isShared_4182_ = v_isSharedCheck_4186_;
                        state = 55;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4179_);
                        crate::leanh::lean_dec(v___x_3816_);
                        v___x_4181_ = crate::leanh::lean_box(0);
                        v_isShared_4182_ = v_isSharedCheck_4186_;
                        state = 55;
                        continue;
                    }
                }
            }
            1 => {
                if v_progress_3729_ == 0 {
                    crate::leanh::lean_dec(v_goal_3730_);
                    v___x_3731_ = crate::leanh::lean_box(0);
                    v___x_3732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3732_, 0, v___x_3731_);
                    return v___x_3732_;
                } else {
                    v___x_3733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3733_, 0, v_goal_3730_);
                    v___x_3734_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3734_, 0, v___x_3733_);
                    return v___x_3734_;
                }
            }
            2 => {
                v___x_3751_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_goal_3738_);
                crate::leanh::lean_inc_ref(v_downPureIntroRule_3740_);
                v___x_3752_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_downPureIntroRule_3740_,
                        v_goal_3738_,
                        v___x_3751_,
                        v___y_3739_,
                        v___y_3741_,
                        v___y_3742_,
                        v___y_3743_,
                        v___y_3744_,
                        v___y_3745_,
                        v___y_3746_,
                        v___y_3747_,
                        v___y_3748_,
                        v___y_3749_,
                        v___y_3750_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3752_) == 0 {
                    v_a_3753_ = crate::leanh::lean_ctor_get(v___x_3752_, 0);
                    crate::leanh::lean_inc(v_a_3753_);
                    crate::leanh::lean_dec_ref_known(v___x_3752_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3753_) == 1 {
                        v_mvarIds_3754_ = crate::leanh::lean_ctor_get(v_a_3753_, 0);
                        crate::leanh::lean_inc(v_mvarIds_3754_);
                        crate::leanh::lean_dec_ref_known(v_a_3753_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_3754_) == 1 {
                            v_tail_3755_ = crate::leanh::lean_ctor_get(v_mvarIds_3754_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_3755_) == 0 {
                                crate::leanh::lean_dec(v_goal_3738_);
                                v_head_3756_ = crate::leanh::lean_ctor_get(v_mvarIds_3754_, 0);
                                crate::leanh::lean_inc(v_head_3756_);
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3754_, 2);
                                v_progress_3729_ = v___y_3736_;
                                v_goal_3730_ = v_head_3756_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3754_, 2);
                                v_progress_3729_ = v_progress_3737_;
                                v_goal_3730_ = v_goal_3738_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_3754_);
                            v_progress_3729_ = v_progress_3737_;
                            v_goal_3730_ = v_goal_3738_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3753_);
                        v_progress_3729_ = v_progress_3737_;
                        v_goal_3730_ = v_goal_3738_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_3738_);
                    v_a_3757_ = crate::leanh::lean_ctor_get(v___x_3752_, 0);
                    v_isSharedCheck_3764_ = (!crate::leanh::lean_is_exclusive(v___x_3752_)) as u8;
                    if v_isSharedCheck_3764_ == 0 {
                        v___x_3759_ = v___x_3752_;
                        v_isShared_3760_ = v_isSharedCheck_3764_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3757_);
                        crate::leanh::lean_dec(v___x_3752_);
                        v___x_3759_ = crate::leanh::lean_box(0);
                        v_isShared_3760_ = v_isSharedCheck_3764_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3760_ == 0 {
                    v___x_3762_ = v___x_3759_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
                    v___x_3762_ = v_reuseFailAlloc_3763_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3762_;
            }
            5 => {
                v___x_3782_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_goal_3768_);
                crate::leanh::lean_inc_ref(v_pureIntroRule_3771_);
                v___x_3783_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_pureIntroRule_3771_,
                        v_goal_3768_,
                        v___x_3782_,
                        v___y_3769_,
                        v___y_3772_,
                        v___y_3773_,
                        v___y_3774_,
                        v___y_3775_,
                        v___y_3776_,
                        v___y_3777_,
                        v___y_3778_,
                        v___y_3779_,
                        v___y_3780_,
                        v___y_3781_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3783_) == 0 {
                    v_a_3784_ = crate::leanh::lean_ctor_get(v___x_3783_, 0);
                    crate::leanh::lean_inc(v_a_3784_);
                    crate::leanh::lean_dec_ref_known(v___x_3783_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3784_) == 1 {
                        v_mvarIds_3785_ = crate::leanh::lean_ctor_get(v_a_3784_, 0);
                        crate::leanh::lean_inc(v_mvarIds_3785_);
                        crate::leanh::lean_dec_ref_known(v_a_3784_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_3785_) == 1 {
                            v_tail_3786_ = crate::leanh::lean_ctor_get(v_mvarIds_3785_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_3786_) == 0 {
                                crate::leanh::lean_dec(v_goal_3768_);
                                v_head_3787_ = crate::leanh::lean_ctor_get(v_mvarIds_3785_, 0);
                                crate::leanh::lean_inc(v_head_3787_);
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3785_, 2);
                                v___y_3736_ = v___y_3766_;
                                v_progress_3737_ = v___y_3766_;
                                v_goal_3738_ = v_head_3787_;
                                v___y_3739_ = v___y_3769_;
                                v_downPureIntroRule_3740_ = v_downPureIntroRule_3770_;
                                v___y_3741_ = v___y_3772_;
                                v___y_3742_ = v___y_3773_;
                                v___y_3743_ = v___y_3774_;
                                v___y_3744_ = v___y_3775_;
                                v___y_3745_ = v___y_3776_;
                                v___y_3746_ = v___y_3777_;
                                v___y_3747_ = v___y_3778_;
                                v___y_3748_ = v___y_3779_;
                                v___y_3749_ = v___y_3780_;
                                v___y_3750_ = v___y_3781_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3785_, 2);
                                v___y_3736_ = v___y_3766_;
                                v_progress_3737_ = v_progress_3767_;
                                v_goal_3738_ = v_goal_3768_;
                                v___y_3739_ = v___y_3769_;
                                v_downPureIntroRule_3740_ = v_downPureIntroRule_3770_;
                                v___y_3741_ = v___y_3772_;
                                v___y_3742_ = v___y_3773_;
                                v___y_3743_ = v___y_3774_;
                                v___y_3744_ = v___y_3775_;
                                v___y_3745_ = v___y_3776_;
                                v___y_3746_ = v___y_3777_;
                                v___y_3747_ = v___y_3778_;
                                v___y_3748_ = v___y_3779_;
                                v___y_3749_ = v___y_3780_;
                                v___y_3750_ = v___y_3781_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_3785_);
                            v___y_3736_ = v___y_3766_;
                            v_progress_3737_ = v_progress_3767_;
                            v_goal_3738_ = v_goal_3768_;
                            v___y_3739_ = v___y_3769_;
                            v_downPureIntroRule_3740_ = v_downPureIntroRule_3770_;
                            v___y_3741_ = v___y_3772_;
                            v___y_3742_ = v___y_3773_;
                            v___y_3743_ = v___y_3774_;
                            v___y_3744_ = v___y_3775_;
                            v___y_3745_ = v___y_3776_;
                            v___y_3746_ = v___y_3777_;
                            v___y_3747_ = v___y_3778_;
                            v___y_3748_ = v___y_3779_;
                            v___y_3749_ = v___y_3780_;
                            v___y_3750_ = v___y_3781_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3784_);
                        v___y_3736_ = v___y_3766_;
                        v_progress_3737_ = v_progress_3767_;
                        v_goal_3738_ = v_goal_3768_;
                        v___y_3739_ = v___y_3769_;
                        v_downPureIntroRule_3740_ = v_downPureIntroRule_3770_;
                        v___y_3741_ = v___y_3772_;
                        v___y_3742_ = v___y_3773_;
                        v___y_3743_ = v___y_3774_;
                        v___y_3744_ = v___y_3775_;
                        v___y_3745_ = v___y_3776_;
                        v___y_3746_ = v___y_3777_;
                        v___y_3747_ = v___y_3778_;
                        v___y_3748_ = v___y_3779_;
                        v___y_3749_ = v___y_3780_;
                        v___y_3750_ = v___y_3781_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_3768_);
                    v_a_3788_ = crate::leanh::lean_ctor_get(v___x_3783_, 0);
                    v_isSharedCheck_3795_ = (!crate::leanh::lean_is_exclusive(v___x_3783_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v___x_3790_ = v___x_3783_;
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3788_);
                        crate::leanh::lean_dec(v___x_3783_);
                        v___x_3790_ = crate::leanh::lean_box(0);
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3791_ == 0 {
                    v___x_3793_ = v___x_3790_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
                    v___x_3793_ = v_reuseFailAlloc_3794_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3793_;
            }
            8 => {
                v___x_3802_ = l_Lean_MVarId_getType(
                    v___y_3797_,
                    v___y_3798_,
                    v___y_3799_,
                    v___y_3800_,
                    v___y_3801_,
                );
                if crate::leanh::lean_obj_tag(v___x_3802_) == 0 {
                    v_a_3803_ = crate::leanh::lean_ctor_get(v___x_3802_, 0);
                    crate::leanh::lean_inc(v_a_3803_);
                    crate::leanh::lean_dec_ref_known(v___x_3802_, 1);
                    v___x_3804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solvePostCondEntails___lam__0___closed__1);
                    v___x_3805_ = l_Lean_MessageData_ofExpr(v_a_3803_);
                    v___x_3806_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3806_, 0, v___x_3804_);
                    crate::leanh::lean_ctor_set(v___x_3806_, 1, v___x_3805_);
                    v___x_3807_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3806_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
                    return v___x_3807_;
                } else {
                    v_a_3808_ = crate::leanh::lean_ctor_get(v___x_3802_, 0);
                    v_isSharedCheck_3815_ = (!crate::leanh::lean_is_exclusive(v___x_3802_)) as u8;
                    if v_isSharedCheck_3815_ == 0 {
                        v___x_3810_ = v___x_3802_;
                        v_isShared_3811_ = v_isSharedCheck_3815_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3808_);
                        crate::leanh::lean_dec(v___x_3802_);
                        v___x_3810_ = crate::leanh::lean_box(0);
                        v_isShared_3811_ = v_isSharedCheck_3815_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3811_ == 0 {
                    v___x_3813_ = v___x_3810_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
                    v___x_3813_ = v_reuseFailAlloc_3814_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3813_;
            }
            11 => {
                v___x_3826_ = l_Lean_Expr_cleanupAnnotations(v_a_3817_);
                v___x_3827_ = l_Lean_Expr_isApp(v___x_3826_);
                if v___x_3827_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3826_);
                    crate::leanh::lean_dec(v_goal_3715_);
                    state = 12;
                    continue;
                } else {
                    v_arg_3828_ = crate::leanh::lean_ctor_get(v___x_3826_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3828_);
                    v___x_3829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3826_);
                    v___x_3830_ = l_Lean_Expr_isApp(v___x_3829_);
                    if v___x_3830_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3829_);
                        crate::leanh::lean_dec_ref(v_arg_3828_);
                        crate::leanh::lean_dec(v_goal_3715_);
                        state = 12;
                        continue;
                    } else {
                        v_arg_3831_ = crate::leanh::lean_ctor_get(v___x_3829_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3831_);
                        v___x_3832_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3829_);
                        v___x_3833_ = l_Lean_Expr_isApp(v___x_3832_);
                        if v___x_3833_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3832_);
                            crate::leanh::lean_dec_ref(v_arg_3831_);
                            crate::leanh::lean_dec_ref(v_arg_3828_);
                            crate::leanh::lean_dec(v_goal_3715_);
                            state = 12;
                            continue;
                        } else {
                            v___x_3834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3832_);
                            v___x_3835_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP___lam__0___closed__6;
                            v_progress_3836_ = l_Lean_Expr_isConstOf(v___x_3834_, v___x_3835_);
                            crate::leanh::lean_dec_ref(v___x_3834_);
                            if v_progress_3836_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_3831_);
                                crate::leanh::lean_dec_ref(v_arg_3828_);
                                crate::leanh::lean_dec(v_goal_3715_);
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_3819_);
                                v_progress_3837_ = 0;
                                v___x_3884_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__5;
                                v___x_4173_ = crate::leanh::lean_unsigned_to_nat(2);
                                v___x_4174_ =
                                    l_Lean_Expr_isAppOfArity(v_arg_3831_, v___x_3884_, v___x_4173_);
                                if v___x_4174_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_3831_);
                                    v___x_4175_ = crate::leanh::lean_box(0);
                                    v___y_4167_ = v___x_4175_;
                                    state = 54;
                                    continue;
                                } else {
                                    v___x_4176_ = l_Lean_Expr_appArg_x21(v_arg_3831_);
                                    crate::leanh::lean_dec_ref(v_arg_3831_);
                                    v___x_4177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4177_, 0, v___x_4176_);
                                    v___y_4167_ = v___x_4177_;
                                    state = 54;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            12 => {
                v___x_3822_ = crate::leanh::lean_box(0);
                if v_isShared_3820_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3819_, 0, v___x_3822_);
                    v___x_3824_ = v___x_3819_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
                    v___x_3824_ = v_reuseFailAlloc_3825_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3824_;
            }
            14 => {
                v_downPureIntroRule_3853_ = crate::leanh::lean_ctor_get(v___y_3850_, 5);
                v_pureElimRule_3854_ = crate::leanh::lean_ctor_get(v___y_3850_, 6);
                v_pureIntroRule_3855_ = crate::leanh::lean_ctor_get(v___y_3850_, 7);
                v___x_3856_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_3840_);
                crate::leanh::lean_inc_ref(v_pureElimRule_3854_);
                v___x_3857_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_pureElimRule_3854_,
                        v___y_3840_,
                        v___x_3856_,
                        v___y_3850_,
                        v___y_3843_,
                        v___y_3847_,
                        v___y_3849_,
                        v___y_3844_,
                        v___y_3841_,
                        v___y_3851_,
                        v___y_3846_,
                        v___y_3842_,
                        v___y_3848_,
                        v___y_3839_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3857_) == 0 {
                    v_a_3858_ = crate::leanh::lean_ctor_get(v___x_3857_, 0);
                    crate::leanh::lean_inc(v_a_3858_);
                    crate::leanh::lean_dec_ref_known(v___x_3857_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3858_) == 1 {
                        v_mvarIds_3859_ = crate::leanh::lean_ctor_get(v_a_3858_, 0);
                        crate::leanh::lean_inc(v_mvarIds_3859_);
                        crate::leanh::lean_dec_ref_known(v_a_3858_, 1);
                        if crate::leanh::lean_obj_tag(v_mvarIds_3859_) == 1 {
                            v_tail_3860_ = crate::leanh::lean_ctor_get(v_mvarIds_3859_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_3860_) == 0 {
                                crate::leanh::lean_dec(v___y_3845_);
                                crate::leanh::lean_dec(v___y_3840_);
                                v_head_3861_ = crate::leanh::lean_ctor_get(v_mvarIds_3859_, 0);
                                crate::leanh::lean_inc(v_head_3861_);
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3859_, 2);
                                v___x_3862_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3);
                                v___x_3863_ =
                                    l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
                                        v_head_3861_,
                                        v___x_3862_,
                                        v___y_3850_,
                                        v___y_3843_,
                                        v___y_3841_,
                                        v___y_3851_,
                                        v___y_3846_,
                                        v___y_3842_,
                                        v___y_3848_,
                                        v___y_3839_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_3863_) == 0 {
                                    v_a_3864_ = crate::leanh::lean_ctor_get(v___x_3863_, 0);
                                    crate::leanh::lean_inc(v_a_3864_);
                                    crate::leanh::lean_dec_ref_known(v___x_3863_, 1);
                                    v___y_3766_ = v___y_3852_;
                                    v_progress_3767_ = v___y_3852_;
                                    v_goal_3768_ = v_a_3864_;
                                    v___y_3769_ = v___y_3850_;
                                    v_downPureIntroRule_3770_ = v_downPureIntroRule_3853_;
                                    v_pureIntroRule_3771_ = v_pureIntroRule_3855_;
                                    v___y_3772_ = v___y_3843_;
                                    v___y_3773_ = v___y_3847_;
                                    v___y_3774_ = v___y_3849_;
                                    v___y_3775_ = v___y_3844_;
                                    v___y_3776_ = v___y_3841_;
                                    v___y_3777_ = v___y_3851_;
                                    v___y_3778_ = v___y_3846_;
                                    v___y_3779_ = v___y_3842_;
                                    v___y_3780_ = v___y_3848_;
                                    v___y_3781_ = v___y_3839_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_a_3865_ = crate::leanh::lean_ctor_get(v___x_3863_, 0);
                                    v_isSharedCheck_3872_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3863_)) as u8;
                                    if v_isSharedCheck_3872_ == 0 {
                                        v___x_3867_ = v___x_3863_;
                                        v_isShared_3868_ = v_isSharedCheck_3872_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3865_);
                                        crate::leanh::lean_dec(v___x_3863_);
                                        v___x_3867_ = crate::leanh::lean_box(0);
                                        v_isShared_3868_ = v_isSharedCheck_3872_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_mvarIds_3859_, 2);
                                v___x_3873_ = (crate::leanh::lean_unbox(v___y_3845_) as u8);
                                crate::leanh::lean_dec(v___y_3845_);
                                v___y_3766_ = v___y_3852_;
                                v_progress_3767_ = v___x_3873_;
                                v_goal_3768_ = v___y_3840_;
                                v___y_3769_ = v___y_3850_;
                                v_downPureIntroRule_3770_ = v_downPureIntroRule_3853_;
                                v_pureIntroRule_3771_ = v_pureIntroRule_3855_;
                                v___y_3772_ = v___y_3843_;
                                v___y_3773_ = v___y_3847_;
                                v___y_3774_ = v___y_3849_;
                                v___y_3775_ = v___y_3844_;
                                v___y_3776_ = v___y_3841_;
                                v___y_3777_ = v___y_3851_;
                                v___y_3778_ = v___y_3846_;
                                v___y_3779_ = v___y_3842_;
                                v___y_3780_ = v___y_3848_;
                                v___y_3781_ = v___y_3839_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarIds_3859_);
                            v___x_3874_ = (crate::leanh::lean_unbox(v___y_3845_) as u8);
                            crate::leanh::lean_dec(v___y_3845_);
                            v___y_3766_ = v___y_3852_;
                            v_progress_3767_ = v___x_3874_;
                            v_goal_3768_ = v___y_3840_;
                            v___y_3769_ = v___y_3850_;
                            v_downPureIntroRule_3770_ = v_downPureIntroRule_3853_;
                            v_pureIntroRule_3771_ = v_pureIntroRule_3855_;
                            v___y_3772_ = v___y_3843_;
                            v___y_3773_ = v___y_3847_;
                            v___y_3774_ = v___y_3849_;
                            v___y_3775_ = v___y_3844_;
                            v___y_3776_ = v___y_3841_;
                            v___y_3777_ = v___y_3851_;
                            v___y_3778_ = v___y_3846_;
                            v___y_3779_ = v___y_3842_;
                            v___y_3780_ = v___y_3848_;
                            v___y_3781_ = v___y_3839_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3858_);
                        v___x_3875_ = (crate::leanh::lean_unbox(v___y_3845_) as u8);
                        crate::leanh::lean_dec(v___y_3845_);
                        v___y_3766_ = v___y_3852_;
                        v_progress_3767_ = v___x_3875_;
                        v_goal_3768_ = v___y_3840_;
                        v___y_3769_ = v___y_3850_;
                        v_downPureIntroRule_3770_ = v_downPureIntroRule_3853_;
                        v_pureIntroRule_3771_ = v_pureIntroRule_3855_;
                        v___y_3772_ = v___y_3843_;
                        v___y_3773_ = v___y_3847_;
                        v___y_3774_ = v___y_3849_;
                        v___y_3775_ = v___y_3844_;
                        v___y_3776_ = v___y_3841_;
                        v___y_3777_ = v___y_3851_;
                        v___y_3778_ = v___y_3846_;
                        v___y_3779_ = v___y_3842_;
                        v___y_3780_ = v___y_3848_;
                        v___y_3781_ = v___y_3839_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3845_);
                    crate::leanh::lean_dec(v___y_3840_);
                    v_a_3876_ = crate::leanh::lean_ctor_get(v___x_3857_, 0);
                    v_isSharedCheck_3883_ = (!crate::leanh::lean_is_exclusive(v___x_3857_)) as u8;
                    if v_isSharedCheck_3883_ == 0 {
                        v___x_3878_ = v___x_3857_;
                        v_isShared_3879_ = v_isSharedCheck_3883_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3876_);
                        crate::leanh::lean_dec(v___x_3857_);
                        v___x_3878_ = crate::leanh::lean_box(0);
                        v_isShared_3879_ = v_isSharedCheck_3883_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_3868_ == 0 {
                    v___x_3870_ = v___x_3867_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
                    v___x_3870_ = v_reuseFailAlloc_3871_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3870_;
            }
            17 => {
                if v_isShared_3879_ == 0 {
                    v___x_3881_ = v___x_3878_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_a_3876_);
                    v___x_3881_ = v_reuseFailAlloc_3882_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3881_;
            }
            19 => {
                v___x_3899_ = crate::leanh::lean_box((v_progress_3887_) as usize);
                v___x_3900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3900_, 0, v___x_3899_);
                crate::leanh::lean_ctor_set(v___x_3900_, 1, v___y_3886_);
                v___x_3901_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_3836_, v___x_3900_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
                if crate::leanh::lean_obj_tag(v___x_3901_) == 0 {
                    v_a_3902_ = crate::leanh::lean_ctor_get(v___x_3901_, 0);
                    crate::leanh::lean_inc(v_a_3902_);
                    crate::leanh::lean_dec_ref_known(v___x_3901_, 1);
                    v_fst_3903_ = crate::leanh::lean_ctor_get(v_a_3902_, 0);
                    crate::leanh::lean_inc(v_fst_3903_);
                    v_snd_3904_ = crate::leanh::lean_ctor_get(v_a_3902_, 1);
                    crate::leanh::lean_inc_n(v_snd_3904_, 2);
                    crate::leanh::lean_dec(v_a_3902_);
                    v___x_3905_ = l_Lean_MVarId_getType(
                        v_snd_3904_,
                        v___y_3895_,
                        v___y_3896_,
                        v___y_3897_,
                        v___y_3898_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3905_) == 0 {
                        v_a_3906_ = crate::leanh::lean_ctor_get(v___x_3905_, 0);
                        crate::leanh::lean_inc(v_a_3906_);
                        crate::leanh::lean_dec_ref_known(v___x_3905_, 1);
                        v___x_3907_ = l_Lean_Expr_cleanupAnnotations(v_a_3906_);
                        v___x_3908_ = l_Lean_Expr_isApp(v___x_3907_);
                        if v___x_3908_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3907_);
                            crate::leanh::lean_dec(v_fst_3903_);
                            v___y_3797_ = v_snd_3904_;
                            v___y_3798_ = v___y_3895_;
                            v___y_3799_ = v___y_3896_;
                            v___y_3800_ = v___y_3897_;
                            v___y_3801_ = v___y_3898_;
                            state = 8;
                            continue;
                        } else {
                            v___x_3909_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3907_);
                            v___x_3910_ = l_Lean_Expr_isApp(v___x_3909_);
                            if v___x_3910_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3909_);
                                crate::leanh::lean_dec(v_fst_3903_);
                                v___y_3797_ = v_snd_3904_;
                                v___y_3798_ = v___y_3895_;
                                v___y_3799_ = v___y_3896_;
                                v___y_3800_ = v___y_3897_;
                                v___y_3801_ = v___y_3898_;
                                state = 8;
                                continue;
                            } else {
                                v_arg_3911_ = crate::leanh::lean_ctor_get(v___x_3909_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3911_);
                                v___x_3912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3909_);
                                v___x_3913_ = l_Lean_Expr_isApp(v___x_3912_);
                                if v___x_3913_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3912_);
                                    crate::leanh::lean_dec_ref(v_arg_3911_);
                                    crate::leanh::lean_dec(v_fst_3903_);
                                    v___y_3797_ = v_snd_3904_;
                                    v___y_3798_ = v___y_3895_;
                                    v___y_3799_ = v___y_3896_;
                                    v___y_3800_ = v___y_3897_;
                                    v___y_3801_ = v___y_3898_;
                                    state = 8;
                                    continue;
                                } else {
                                    v___x_3914_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3912_);
                                    v___x_3915_ = l_Lean_Expr_isConstOf(v___x_3914_, v___x_3835_);
                                    crate::leanh::lean_dec_ref(v___x_3914_);
                                    if v___x_3915_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_3911_);
                                        crate::leanh::lean_dec(v_fst_3903_);
                                        v___y_3797_ = v_snd_3904_;
                                        v___y_3798_ = v___y_3895_;
                                        v___y_3799_ = v___y_3896_;
                                        v___y_3800_ = v___y_3897_;
                                        v___y_3801_ = v___y_3898_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_3916_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_3917_ = l_Lean_Expr_isAppOfArity(
                                            v_arg_3911_,
                                            v___x_3884_,
                                            v___x_3916_,
                                        );
                                        if v___x_3917_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_3911_);
                                            v_entailsNilIntroRule_3918_ =
                                                crate::leanh::lean_ctor_get(v___y_3888_, 2);
                                            v_downPureIntroRule_3919_ =
                                                crate::leanh::lean_ctor_get(v___y_3888_, 5);
                                            v___x_3920_ = crate::leanh::lean_box(0);
                                            crate::leanh::lean_inc(v_snd_3904_);
                                            crate::leanh::lean_inc_ref(v_entailsNilIntroRule_3918_);
                                            v___x_3921_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_entailsNilIntroRule_3918_, v_snd_3904_, v___x_3920_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
                                            if crate::leanh::lean_obj_tag(v___x_3921_) == 0 {
                                                v_a_3922_ =
                                                    crate::leanh::lean_ctor_get(v___x_3921_, 0);
                                                crate::leanh::lean_inc(v_a_3922_);
                                                crate::leanh::lean_dec_ref_known(v___x_3921_, 1);
                                                if crate::leanh::lean_obj_tag(v_a_3922_) == 1 {
                                                    v_mvarIds_3923_ =
                                                        crate::leanh::lean_ctor_get(v_a_3922_, 0);
                                                    crate::leanh::lean_inc(v_mvarIds_3923_);
                                                    crate::leanh::lean_dec_ref_known(v_a_3922_, 1);
                                                    if crate::leanh::lean_obj_tag(v_mvarIds_3923_)
                                                        == 1
                                                    {
                                                        v_tail_3924_ = crate::leanh::lean_ctor_get(
                                                            v_mvarIds_3923_,
                                                            1,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v_tail_3924_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec(v_snd_3904_);
                                                            crate::leanh::lean_dec(v_fst_3903_);
                                                            v_head_3925_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_mvarIds_3923_,
                                                                    0,
                                                                );
                                                            crate::leanh::lean_inc(v_head_3925_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_mvarIds_3923_,
                                                                2,
                                                            );
                                                            v___x_3926_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__9);
                                                            v___x_3927_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(v_head_3925_, v___x_3926_, v___y_3888_, v___y_3889_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3927_,
                                                            ) == 0
                                                            {
                                                                v_a_3928_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3927_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_3928_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_3927_,
                                                                    1,
                                                                );
                                                                v___y_3736_ = v___x_3915_;
                                                                v_progress_3737_ = v___x_3915_;
                                                                v_goal_3738_ = v_a_3928_;
                                                                v___y_3739_ = v___y_3888_;
                                                                v_downPureIntroRule_3740_ =
                                                                    v_downPureIntroRule_3919_;
                                                                v___y_3741_ = v___y_3889_;
                                                                v___y_3742_ = v___y_3890_;
                                                                v___y_3743_ = v___y_3891_;
                                                                v___y_3744_ = v___y_3892_;
                                                                v___y_3745_ = v___y_3893_;
                                                                v___y_3746_ = v___y_3894_;
                                                                v___y_3747_ = v___y_3895_;
                                                                v___y_3748_ = v___y_3896_;
                                                                v___y_3749_ = v___y_3897_;
                                                                v___y_3750_ = v___y_3898_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                v_a_3929_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3927_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3936_ = (!crate::leanh::lean_is_exclusive(v___x_3927_)) as u8;
                                                                if v_isSharedCheck_3936_ == 0 {
                                                                    v___x_3931_ = v___x_3927_;
                                                                    v_isShared_3932_ =
                                                                        v_isSharedCheck_3936_;
                                                                    state = 20;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_3929_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_3927_,
                                                                    );
                                                                    v___x_3931_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3932_ =
                                                                        v_isSharedCheck_3936_;
                                                                    state = 20;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_mvarIds_3923_,
                                                                2,
                                                            );
                                                            v___x_3937_ = (crate::leanh::lean_unbox(
                                                                v_fst_3903_,
                                                            )
                                                                as u8);
                                                            crate::leanh::lean_dec(v_fst_3903_);
                                                            v___y_3736_ = v___x_3915_;
                                                            v_progress_3737_ = v___x_3937_;
                                                            v_goal_3738_ = v_snd_3904_;
                                                            v___y_3739_ = v___y_3888_;
                                                            v_downPureIntroRule_3740_ =
                                                                v_downPureIntroRule_3919_;
                                                            v___y_3741_ = v___y_3889_;
                                                            v___y_3742_ = v___y_3890_;
                                                            v___y_3743_ = v___y_3891_;
                                                            v___y_3744_ = v___y_3892_;
                                                            v___y_3745_ = v___y_3893_;
                                                            v___y_3746_ = v___y_3894_;
                                                            v___y_3747_ = v___y_3895_;
                                                            v___y_3748_ = v___y_3896_;
                                                            v___y_3749_ = v___y_3897_;
                                                            v___y_3750_ = v___y_3898_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_mvarIds_3923_);
                                                        v___x_3938_ =
                                                            (crate::leanh::lean_unbox(v_fst_3903_)
                                                                as u8);
                                                        crate::leanh::lean_dec(v_fst_3903_);
                                                        v___y_3736_ = v___x_3915_;
                                                        v_progress_3737_ = v___x_3938_;
                                                        v_goal_3738_ = v_snd_3904_;
                                                        v___y_3739_ = v___y_3888_;
                                                        v_downPureIntroRule_3740_ =
                                                            v_downPureIntroRule_3919_;
                                                        v___y_3741_ = v___y_3889_;
                                                        v___y_3742_ = v___y_3890_;
                                                        v___y_3743_ = v___y_3891_;
                                                        v___y_3744_ = v___y_3892_;
                                                        v___y_3745_ = v___y_3893_;
                                                        v___y_3746_ = v___y_3894_;
                                                        v___y_3747_ = v___y_3895_;
                                                        v___y_3748_ = v___y_3896_;
                                                        v___y_3749_ = v___y_3897_;
                                                        v___y_3750_ = v___y_3898_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_3922_);
                                                    v___x_3939_ =
                                                        (crate::leanh::lean_unbox(v_fst_3903_)
                                                            as u8);
                                                    crate::leanh::lean_dec(v_fst_3903_);
                                                    v___y_3736_ = v___x_3915_;
                                                    v_progress_3737_ = v___x_3939_;
                                                    v_goal_3738_ = v_snd_3904_;
                                                    v___y_3739_ = v___y_3888_;
                                                    v_downPureIntroRule_3740_ =
                                                        v_downPureIntroRule_3919_;
                                                    v___y_3741_ = v___y_3889_;
                                                    v___y_3742_ = v___y_3890_;
                                                    v___y_3743_ = v___y_3891_;
                                                    v___y_3744_ = v___y_3892_;
                                                    v___y_3745_ = v___y_3893_;
                                                    v___y_3746_ = v___y_3894_;
                                                    v___y_3747_ = v___y_3895_;
                                                    v___y_3748_ = v___y_3896_;
                                                    v___y_3749_ = v___y_3897_;
                                                    v___y_3750_ = v___y_3898_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_snd_3904_);
                                                crate::leanh::lean_dec(v_fst_3903_);
                                                v_a_3940_ =
                                                    crate::leanh::lean_ctor_get(v___x_3921_, 0);
                                                v_isSharedCheck_3947_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3921_))
                                                        as u8;
                                                if v_isSharedCheck_3947_ == 0 {
                                                    v___x_3942_ = v___x_3921_;
                                                    v_isShared_3943_ = v_isSharedCheck_3947_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3940_);
                                                    crate::leanh::lean_dec(v___x_3921_);
                                                    v___x_3942_ = crate::leanh::lean_box(0);
                                                    v_isShared_3943_ = v_isSharedCheck_3947_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___x_3948_ = l_Lean_Expr_appArg_x21(v_arg_3911_);
                                            crate::leanh::lean_dec_ref(v_arg_3911_);
                                            if crate::leanh::lean_obj_tag(v___x_3948_) == 4 {
                                                v_declName_3949_ =
                                                    crate::leanh::lean_ctor_get(v___x_3948_, 0);
                                                crate::leanh::lean_inc(v_declName_3949_);
                                                crate::leanh::lean_dec_ref_known(v___x_3948_, 2);
                                                if crate::leanh::lean_obj_tag(v_declName_3949_) == 1
                                                {
                                                    v_pre_3950_ = crate::leanh::lean_ctor_get(
                                                        v_declName_3949_,
                                                        0,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v_pre_3950_) == 0
                                                    {
                                                        v_str_3951_ = crate::leanh::lean_ctor_get(
                                                            v_declName_3949_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_str_3951_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_declName_3949_,
                                                            2,
                                                        );
                                                        v___x_3952_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__10;
                                                        v___x_3953_ = lean_string_dec_eq(
                                                            v_str_3951_,
                                                            v___x_3952_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_str_3951_);
                                                        if v___x_3953_ == 0 {
                                                            v___y_3839_ = v___y_3898_;
                                                            v___y_3840_ = v_snd_3904_;
                                                            v___y_3841_ = v___y_3893_;
                                                            v___y_3842_ = v___y_3896_;
                                                            v___y_3843_ = v___y_3889_;
                                                            v___y_3844_ = v___y_3892_;
                                                            v___y_3845_ = v_fst_3903_;
                                                            v___y_3846_ = v___y_3895_;
                                                            v___y_3847_ = v___y_3890_;
                                                            v___y_3848_ = v___y_3897_;
                                                            v___y_3849_ = v___y_3891_;
                                                            v___y_3850_ = v___y_3888_;
                                                            v___y_3851_ = v___y_3894_;
                                                            v___y_3852_ = v___x_3915_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            if v___x_3915_ == 0 {
                                                                v___y_3839_ = v___y_3898_;
                                                                v___y_3840_ = v_snd_3904_;
                                                                v___y_3841_ = v___y_3893_;
                                                                v___y_3842_ = v___y_3896_;
                                                                v___y_3843_ = v___y_3889_;
                                                                v___y_3844_ = v___y_3892_;
                                                                v___y_3845_ = v_fst_3903_;
                                                                v___y_3846_ = v___y_3895_;
                                                                v___y_3847_ = v___y_3890_;
                                                                v___y_3848_ = v___y_3897_;
                                                                v___y_3849_ = v___y_3891_;
                                                                v___y_3850_ = v___y_3888_;
                                                                v___y_3851_ = v___y_3894_;
                                                                v___y_3852_ = v___x_3915_;
                                                                state = 14;
                                                                continue;
                                                            } else {
                                                                v_downPureIntroRule_3954_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___y_3888_,
                                                                        5,
                                                                    );
                                                                v_pureIntroRule_3955_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___y_3888_,
                                                                        7,
                                                                    );
                                                                v___x_3956_ =
                                                                    (crate::leanh::lean_unbox(
                                                                        v_fst_3903_,
                                                                    )
                                                                        as u8);
                                                                crate::leanh::lean_dec(v_fst_3903_);
                                                                v___y_3766_ = v___x_3915_;
                                                                v_progress_3767_ = v___x_3956_;
                                                                v_goal_3768_ = v_snd_3904_;
                                                                v___y_3769_ = v___y_3888_;
                                                                v_downPureIntroRule_3770_ =
                                                                    v_downPureIntroRule_3954_;
                                                                v_pureIntroRule_3771_ =
                                                                    v_pureIntroRule_3955_;
                                                                v___y_3772_ = v___y_3889_;
                                                                v___y_3773_ = v___y_3890_;
                                                                v___y_3774_ = v___y_3891_;
                                                                v___y_3775_ = v___y_3892_;
                                                                v___y_3776_ = v___y_3893_;
                                                                v___y_3777_ = v___y_3894_;
                                                                v___y_3778_ = v___y_3895_;
                                                                v___y_3779_ = v___y_3896_;
                                                                v___y_3780_ = v___y_3897_;
                                                                v___y_3781_ = v___y_3898_;
                                                                state = 5;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_declName_3949_,
                                                            2,
                                                        );
                                                        v___y_3839_ = v___y_3898_;
                                                        v___y_3840_ = v_snd_3904_;
                                                        v___y_3841_ = v___y_3893_;
                                                        v___y_3842_ = v___y_3896_;
                                                        v___y_3843_ = v___y_3889_;
                                                        v___y_3844_ = v___y_3892_;
                                                        v___y_3845_ = v_fst_3903_;
                                                        v___y_3846_ = v___y_3895_;
                                                        v___y_3847_ = v___y_3890_;
                                                        v___y_3848_ = v___y_3897_;
                                                        v___y_3849_ = v___y_3891_;
                                                        v___y_3850_ = v___y_3888_;
                                                        v___y_3851_ = v___y_3894_;
                                                        v___y_3852_ = v___x_3915_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_declName_3949_);
                                                    v___y_3839_ = v___y_3898_;
                                                    v___y_3840_ = v_snd_3904_;
                                                    v___y_3841_ = v___y_3893_;
                                                    v___y_3842_ = v___y_3896_;
                                                    v___y_3843_ = v___y_3889_;
                                                    v___y_3844_ = v___y_3892_;
                                                    v___y_3845_ = v_fst_3903_;
                                                    v___y_3846_ = v___y_3895_;
                                                    v___y_3847_ = v___y_3890_;
                                                    v___y_3848_ = v___y_3897_;
                                                    v___y_3849_ = v___y_3891_;
                                                    v___y_3850_ = v___y_3888_;
                                                    v___y_3851_ = v___y_3894_;
                                                    v___y_3852_ = v___x_3915_;
                                                    state = 14;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3948_);
                                                v___y_3839_ = v___y_3898_;
                                                v___y_3840_ = v_snd_3904_;
                                                v___y_3841_ = v___y_3893_;
                                                v___y_3842_ = v___y_3896_;
                                                v___y_3843_ = v___y_3889_;
                                                v___y_3844_ = v___y_3892_;
                                                v___y_3845_ = v_fst_3903_;
                                                v___y_3846_ = v___y_3895_;
                                                v___y_3847_ = v___y_3890_;
                                                v___y_3848_ = v___y_3897_;
                                                v___y_3849_ = v___y_3891_;
                                                v___y_3850_ = v___y_3888_;
                                                v___y_3851_ = v___y_3894_;
                                                v___y_3852_ = v___x_3915_;
                                                state = 14;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_3904_);
                        crate::leanh::lean_dec(v_fst_3903_);
                        v_a_3957_ = crate::leanh::lean_ctor_get(v___x_3905_, 0);
                        v_isSharedCheck_3964_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3905_)) as u8;
                        if v_isSharedCheck_3964_ == 0 {
                            v___x_3959_ = v___x_3905_;
                            v_isShared_3960_ = v_isSharedCheck_3964_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3957_);
                            crate::leanh::lean_dec(v___x_3905_);
                            v___x_3959_ = crate::leanh::lean_box(0);
                            v_isShared_3960_ = v_isSharedCheck_3964_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    v_a_3965_ = crate::leanh::lean_ctor_get(v___x_3901_, 0);
                    v_isSharedCheck_3972_ = (!crate::leanh::lean_is_exclusive(v___x_3901_)) as u8;
                    if v_isSharedCheck_3972_ == 0 {
                        v___x_3967_ = v___x_3901_;
                        v_isShared_3968_ = v_isSharedCheck_3972_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3965_);
                        crate::leanh::lean_dec(v___x_3901_);
                        v___x_3967_ = crate::leanh::lean_box(0);
                        v_isShared_3968_ = v_isSharedCheck_3972_;
                        state = 26;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_3932_ == 0 {
                    v___x_3934_ = v___x_3931_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
                    v___x_3934_ = v_reuseFailAlloc_3935_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3934_;
            }
            22 => {
                if v_isShared_3943_ == 0 {
                    v___x_3945_ = v___x_3942_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
                    v___x_3945_ = v_reuseFailAlloc_3946_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3945_;
            }
            24 => {
                if v_isShared_3960_ == 0 {
                    v___x_3962_ = v___x_3959_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3963_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
                    v___x_3962_ = v_reuseFailAlloc_3963_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3962_;
            }
            26 => {
                if v_isShared_3968_ == 0 {
                    v___x_3970_ = v___x_3967_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
                    v___x_3970_ = v_reuseFailAlloc_3971_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3970_;
            }
            28 => {
                v___x_3987_ = l_Lean_MVarId_getType(
                    v___y_3974_,
                    v___y_3983_,
                    v___y_3984_,
                    v___y_3985_,
                    v___y_3986_,
                );
                if crate::leanh::lean_obj_tag(v___x_3987_) == 0 {
                    v_a_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    crate::leanh::lean_inc(v_a_3988_);
                    crate::leanh::lean_dec_ref_known(v___x_3987_, 1);
                    v___x_3989_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__17);
                    v___x_3990_ = l_Lean_MessageData_ofExpr(v_a_3988_);
                    v___x_3991_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3991_, 0, v___x_3989_);
                    crate::leanh::lean_ctor_set(v___x_3991_, 1, v___x_3990_);
                    v___x_3992_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_3991_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
                    v_a_3993_ = crate::leanh::lean_ctor_get(v___x_3992_, 0);
                    v_isSharedCheck_4000_ = (!crate::leanh::lean_is_exclusive(v___x_3992_)) as u8;
                    if v_isSharedCheck_4000_ == 0 {
                        v___x_3995_ = v___x_3992_;
                        v_isShared_3996_ = v_isSharedCheck_4000_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3993_);
                        crate::leanh::lean_dec(v___x_3992_);
                        v___x_3995_ = crate::leanh::lean_box(0);
                        v_isShared_3996_ = v_isSharedCheck_4000_;
                        state = 29;
                        continue;
                    }
                } else {
                    v_a_4001_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    v_isSharedCheck_4008_ = (!crate::leanh::lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_4008_ == 0 {
                        v___x_4003_ = v___x_3987_;
                        v_isShared_4004_ = v_isSharedCheck_4008_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4001_);
                        crate::leanh::lean_dec(v___x_3987_);
                        v___x_4003_ = crate::leanh::lean_box(0);
                        v_isShared_4004_ = v_isSharedCheck_4008_;
                        state = 31;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_3996_ == 0 {
                    v___x_3998_ = v___x_3995_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
                    v___x_3998_ = v_reuseFailAlloc_3999_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3998_;
            }
            31 => {
                if v_isShared_4004_ == 0 {
                    v___x_4006_ = v___x_4003_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
                    v___x_4006_ = v_reuseFailAlloc_4007_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4006_;
            }
            33 => {
                if v_progress_3836_ == 0 {
                    crate::leanh::lean_dec(v___y_4010_);
                    v___y_3886_ = v_goal_4012_;
                    v_progress_3887_ = v_progress_4011_;
                    v___y_3888_ = v___y_4013_;
                    v___y_3889_ = v___y_4014_;
                    v___y_3890_ = v___y_4015_;
                    v___y_3891_ = v___y_4016_;
                    v___y_3892_ = v___y_4017_;
                    v___y_3893_ = v___y_4018_;
                    v___y_3894_ = v___y_4019_;
                    v___y_3895_ = v___y_4020_;
                    v___y_3896_ = v___y_4021_;
                    v___y_3897_ = v___y_4022_;
                    v___y_3898_ = v___y_4023_;
                    state = 19;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___y_4010_) == 0 {
                        v___y_3886_ = v_goal_4012_;
                        v_progress_3887_ = v_progress_4011_;
                        v___y_3888_ = v___y_4013_;
                        v___y_3889_ = v___y_4014_;
                        v___y_3890_ = v___y_4015_;
                        v___y_3891_ = v___y_4016_;
                        v___y_3892_ = v___y_4017_;
                        v___y_3893_ = v___y_4018_;
                        v___y_3894_ = v___y_4019_;
                        v___y_3895_ = v___y_4020_;
                        v___y_3896_ = v___y_4021_;
                        v___y_3897_ = v___y_4022_;
                        v___y_3898_ = v___y_4023_;
                        state = 19;
                        continue;
                    } else {
                        v_isSharedCheck_4052_ =
                            (!crate::leanh::lean_is_exclusive(v___y_4010_)) as u8;
                        if v_isSharedCheck_4052_ == 0 {
                            v_unused_4053_ = crate::leanh::lean_ctor_get(v___y_4010_, 0);
                            crate::leanh::lean_dec(v_unused_4053_);
                            v___x_4025_ = v___y_4010_;
                            v_isShared_4026_ = v_isSharedCheck_4052_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_4010_);
                            v___x_4025_ = crate::leanh::lean_box(0);
                            v_isShared_4026_ = v_isSharedCheck_4052_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            34 => {
                v_pureIntroRule_4027_ = crate::leanh::lean_ctor_get(v___y_4013_, 7);
                v___x_4028_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_goal_4012_);
                crate::leanh::lean_inc_ref(v_pureIntroRule_4027_);
                v___x_4029_ =
                    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                        v_pureIntroRule_4027_,
                        v_goal_4012_,
                        v___x_4028_,
                        v___y_4013_,
                        v___y_4014_,
                        v___y_4015_,
                        v___y_4016_,
                        v___y_4017_,
                        v___y_4018_,
                        v___y_4019_,
                        v___y_4020_,
                        v___y_4021_,
                        v___y_4022_,
                        v___y_4023_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4029_) == 0 {
                    v_a_4030_ = crate::leanh::lean_ctor_get(v___x_4029_, 0);
                    v_isSharedCheck_4043_ = (!crate::leanh::lean_is_exclusive(v___x_4029_)) as u8;
                    if v_isSharedCheck_4043_ == 0 {
                        v___x_4032_ = v___x_4029_;
                        v_isShared_4033_ = v_isSharedCheck_4043_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4030_);
                        crate::leanh::lean_dec(v___x_4029_);
                        v___x_4032_ = crate::leanh::lean_box(0);
                        v_isShared_4033_ = v_isSharedCheck_4043_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4025_);
                    crate::leanh::lean_dec(v_goal_4012_);
                    v_a_4044_ = crate::leanh::lean_ctor_get(v___x_4029_, 0);
                    v_isSharedCheck_4051_ = (!crate::leanh::lean_is_exclusive(v___x_4029_)) as u8;
                    if v_isSharedCheck_4051_ == 0 {
                        v___x_4046_ = v___x_4029_;
                        v_isShared_4047_ = v_isSharedCheck_4051_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4044_);
                        crate::leanh::lean_dec(v___x_4029_);
                        v___x_4046_ = crate::leanh::lean_box(0);
                        v_isShared_4047_ = v_isSharedCheck_4051_;
                        state = 38;
                        continue;
                    }
                }
            }
            35 => {
                if crate::leanh::lean_obj_tag(v_a_4030_) == 1 {
                    v_mvarIds_4034_ = crate::leanh::lean_ctor_get(v_a_4030_, 0);
                    crate::leanh::lean_inc(v_mvarIds_4034_);
                    crate::leanh::lean_dec_ref_known(v_a_4030_, 1);
                    if crate::leanh::lean_obj_tag(v_mvarIds_4034_) == 1 {
                        v_tail_4035_ = crate::leanh::lean_ctor_get(v_mvarIds_4034_, 1);
                        if crate::leanh::lean_obj_tag(v_tail_4035_) == 0 {
                            crate::leanh::lean_dec(v_goal_4012_);
                            v_head_4036_ = crate::leanh::lean_ctor_get(v_mvarIds_4034_, 0);
                            crate::leanh::lean_inc(v_head_4036_);
                            crate::leanh::lean_dec_ref_known(v_mvarIds_4034_, 2);
                            if v_isShared_4026_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4025_, 0, v_head_4036_);
                                v___x_4038_ = v___x_4025_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_4042_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4042_,
                                    0,
                                    v_head_4036_,
                                );
                                v___x_4038_ = v_reuseFailAlloc_4042_;
                                state = 36;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_mvarIds_4034_, 2);
                            crate::leanh::lean_del_object(v___x_4032_);
                            crate::leanh::lean_del_object(v___x_4025_);
                            v___y_3974_ = v_goal_4012_;
                            v___y_3975_ = v_progress_4011_;
                            v___y_3976_ = v___y_4013_;
                            v___y_3977_ = v___y_4014_;
                            v___y_3978_ = v___y_4015_;
                            v___y_3979_ = v___y_4016_;
                            v___y_3980_ = v___y_4017_;
                            v___y_3981_ = v___y_4018_;
                            v___y_3982_ = v___y_4019_;
                            v___y_3983_ = v___y_4020_;
                            v___y_3984_ = v___y_4021_;
                            v___y_3985_ = v___y_4022_;
                            v___y_3986_ = v___y_4023_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarIds_4034_);
                        crate::leanh::lean_del_object(v___x_4032_);
                        crate::leanh::lean_del_object(v___x_4025_);
                        v___y_3974_ = v_goal_4012_;
                        v___y_3975_ = v_progress_4011_;
                        v___y_3976_ = v___y_4013_;
                        v___y_3977_ = v___y_4014_;
                        v___y_3978_ = v___y_4015_;
                        v___y_3979_ = v___y_4016_;
                        v___y_3980_ = v___y_4017_;
                        v___y_3981_ = v___y_4018_;
                        v___y_3982_ = v___y_4019_;
                        v___y_3983_ = v___y_4020_;
                        v___y_3984_ = v___y_4021_;
                        v___y_3985_ = v___y_4022_;
                        v___y_3986_ = v___y_4023_;
                        state = 28;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4032_);
                    crate::leanh::lean_dec(v_a_4030_);
                    crate::leanh::lean_del_object(v___x_4025_);
                    v___y_3974_ = v_goal_4012_;
                    v___y_3975_ = v_progress_4011_;
                    v___y_3976_ = v___y_4013_;
                    v___y_3977_ = v___y_4014_;
                    v___y_3978_ = v___y_4015_;
                    v___y_3979_ = v___y_4016_;
                    v___y_3980_ = v___y_4017_;
                    v___y_3981_ = v___y_4018_;
                    v___y_3982_ = v___y_4019_;
                    v___y_3983_ = v___y_4020_;
                    v___y_3984_ = v___y_4021_;
                    v___y_3985_ = v___y_4022_;
                    v___y_3986_ = v___y_4023_;
                    state = 28;
                    continue;
                }
            }
            36 => {
                if v_isShared_4033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4032_, 0, v___x_4038_);
                    v___x_4040_ = v___x_4032_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
                    v___x_4040_ = v_reuseFailAlloc_4041_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4040_;
            }
            38 => {
                if v_isShared_4047_ == 0 {
                    v___x_4049_ = v___x_4046_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
                    v___x_4049_ = v_reuseFailAlloc_4050_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4049_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v___y_4055_) == 0 {
                    crate::leanh::lean_dec(v___y_4056_);
                    v___y_3886_ = v_goal_4058_;
                    v_progress_3887_ = v_progress_4057_;
                    v___y_3888_ = v___y_4059_;
                    v___y_3889_ = v___y_4060_;
                    v___y_3890_ = v___y_4061_;
                    v___y_3891_ = v___y_4062_;
                    v___y_3892_ = v___y_4063_;
                    v___y_3893_ = v___y_4064_;
                    v___y_3894_ = v___y_4065_;
                    v___y_3895_ = v___y_4066_;
                    v___y_3896_ = v___y_4067_;
                    v___y_3897_ = v___y_4068_;
                    v___y_3898_ = v___y_4069_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_4055_, 1);
                    v___y_4010_ = v___y_4056_;
                    v_progress_4011_ = v_progress_4057_;
                    v_goal_4012_ = v_goal_4058_;
                    v___y_4013_ = v___y_4059_;
                    v___y_4014_ = v___y_4060_;
                    v___y_4015_ = v___y_4061_;
                    v___y_4016_ = v___y_4062_;
                    v___y_4017_ = v___y_4063_;
                    v___y_4018_ = v___y_4064_;
                    v___y_4019_ = v___y_4065_;
                    v___y_4020_ = v___y_4066_;
                    v___y_4021_ = v___y_4067_;
                    v___y_4022_ = v___y_4068_;
                    v___y_4023_ = v___y_4069_;
                    state = 33;
                    continue;
                }
            }
            41 => {
                crate::leanh::lean_dec(v___y_4072_);
                crate::leanh::lean_dec(v___y_4071_);
                v___x_4084_ = l_Lean_MVarId_getType(
                    v_goal_3715_,
                    v___y_4080_,
                    v___y_4081_,
                    v___y_4082_,
                    v___y_4083_,
                );
                if crate::leanh::lean_obj_tag(v___x_4084_) == 0 {
                    v_a_4085_ = crate::leanh::lean_ctor_get(v___x_4084_, 0);
                    crate::leanh::lean_inc(v_a_4085_);
                    crate::leanh::lean_dec_ref_known(v___x_4084_, 1);
                    v___x_4086_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__19);
                    v___x_4087_ = l_Lean_MessageData_ofExpr(v_a_4085_);
                    v___x_4088_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4088_, 0, v___x_4086_);
                    crate::leanh::lean_ctor_set(v___x_4088_, 1, v___x_4087_);
                    v___x_4089_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__0___redArg(v___x_4088_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
                    v_a_4090_ = crate::leanh::lean_ctor_get(v___x_4089_, 0);
                    v_isSharedCheck_4097_ = (!crate::leanh::lean_is_exclusive(v___x_4089_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4092_ = v___x_4089_;
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4090_);
                        crate::leanh::lean_dec(v___x_4089_);
                        v___x_4092_ = crate::leanh::lean_box(0);
                        v_isShared_4093_ = v_isSharedCheck_4097_;
                        state = 42;
                        continue;
                    }
                } else {
                    v_a_4098_ = crate::leanh::lean_ctor_get(v___x_4084_, 0);
                    v_isSharedCheck_4105_ = (!crate::leanh::lean_is_exclusive(v___x_4084_)) as u8;
                    if v_isSharedCheck_4105_ == 0 {
                        v___x_4100_ = v___x_4084_;
                        v_isShared_4101_ = v_isSharedCheck_4105_;
                        state = 44;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4098_);
                        crate::leanh::lean_dec(v___x_4084_);
                        v___x_4100_ = crate::leanh::lean_box(0);
                        v_isShared_4101_ = v_isSharedCheck_4105_;
                        state = 44;
                        continue;
                    }
                }
            }
            42 => {
                if v_isShared_4093_ == 0 {
                    v___x_4095_ = v___x_4092_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4095_;
            }
            44 => {
                if v_isShared_4101_ == 0 {
                    v___x_4103_ = v___x_4100_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
                    v___x_4103_ = v_reuseFailAlloc_4104_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4103_;
            }
            46 => {
                if v_pureHNonTrue_4109_ == 0 {
                    v___y_4055_ = v___y_4107_;
                    v___y_4056_ = v___y_4108_;
                    v_progress_4057_ = v_progress_3837_;
                    v_goal_4058_ = v_goal_3715_;
                    v___y_4059_ = v___y_4110_;
                    v___y_4060_ = v___y_4111_;
                    v___y_4061_ = v___y_4112_;
                    v___y_4062_ = v___y_4113_;
                    v___y_4063_ = v___y_4114_;
                    v___y_4064_ = v___y_4115_;
                    v___y_4065_ = v___y_4116_;
                    v___y_4066_ = v___y_4117_;
                    v___y_4067_ = v___y_4118_;
                    v___y_4068_ = v___y_4119_;
                    v___y_4069_ = v___y_4120_;
                    state = 40;
                    continue;
                } else {
                    v_pureElimRule_4121_ = crate::leanh::lean_ctor_get(v___y_4110_, 6);
                    v___x_4122_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_goal_3715_);
                    crate::leanh::lean_inc_ref(v_pureElimRule_4121_);
                    v___x_4123_ =
                        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                            v_pureElimRule_4121_,
                            v_goal_3715_,
                            v___x_4122_,
                            v___y_4110_,
                            v___y_4111_,
                            v___y_4112_,
                            v___y_4113_,
                            v___y_4114_,
                            v___y_4115_,
                            v___y_4116_,
                            v___y_4117_,
                            v___y_4118_,
                            v___y_4119_,
                            v___y_4120_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4123_) == 0 {
                        v_a_4124_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                        crate::leanh::lean_inc(v_a_4124_);
                        crate::leanh::lean_dec_ref_known(v___x_4123_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4124_) == 1 {
                            v_mvarIds_4125_ = crate::leanh::lean_ctor_get(v_a_4124_, 0);
                            crate::leanh::lean_inc(v_mvarIds_4125_);
                            crate::leanh::lean_dec_ref_known(v_a_4124_, 1);
                            if crate::leanh::lean_obj_tag(v_mvarIds_4125_) == 1 {
                                v_tail_4126_ = crate::leanh::lean_ctor_get(v_mvarIds_4125_, 1);
                                if crate::leanh::lean_obj_tag(v_tail_4126_) == 0 {
                                    crate::leanh::lean_dec(v_goal_3715_);
                                    v_head_4127_ = crate::leanh::lean_ctor_get(v_mvarIds_4125_, 0);
                                    crate::leanh::lean_inc(v_head_4127_);
                                    crate::leanh::lean_dec_ref_known(v_mvarIds_4125_, 2);
                                    v___x_4128_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__3);
                                    v___x_4129_ =
                                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
                                            v_head_4127_,
                                            v___x_4128_,
                                            v___y_4110_,
                                            v___y_4111_,
                                            v___y_4115_,
                                            v___y_4116_,
                                            v___y_4117_,
                                            v___y_4118_,
                                            v___y_4119_,
                                            v___y_4120_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_4129_) == 0 {
                                        v_a_4130_ = crate::leanh::lean_ctor_get(v___x_4129_, 0);
                                        crate::leanh::lean_inc(v_a_4130_);
                                        crate::leanh::lean_dec_ref_known(v___x_4129_, 1);
                                        v___y_4055_ = v___y_4107_;
                                        v___y_4056_ = v___y_4108_;
                                        v_progress_4057_ = v_progress_3836_;
                                        v_goal_4058_ = v_a_4130_;
                                        v___y_4059_ = v___y_4110_;
                                        v___y_4060_ = v___y_4111_;
                                        v___y_4061_ = v___y_4112_;
                                        v___y_4062_ = v___y_4113_;
                                        v___y_4063_ = v___y_4114_;
                                        v___y_4064_ = v___y_4115_;
                                        v___y_4065_ = v___y_4116_;
                                        v___y_4066_ = v___y_4117_;
                                        v___y_4067_ = v___y_4118_;
                                        v___y_4068_ = v___y_4119_;
                                        v___y_4069_ = v___y_4120_;
                                        state = 40;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___y_4108_);
                                        crate::leanh::lean_dec(v___y_4107_);
                                        v_a_4131_ = crate::leanh::lean_ctor_get(v___x_4129_, 0);
                                        v_isSharedCheck_4138_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4129_)) as u8;
                                        if v_isSharedCheck_4138_ == 0 {
                                            v___x_4133_ = v___x_4129_;
                                            v_isShared_4134_ = v_isSharedCheck_4138_;
                                            state = 47;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4131_);
                                            crate::leanh::lean_dec(v___x_4129_);
                                            v___x_4133_ = crate::leanh::lean_box(0);
                                            v_isShared_4134_ = v_isSharedCheck_4138_;
                                            state = 47;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_mvarIds_4125_, 2);
                                    v___y_4071_ = v___y_4107_;
                                    v___y_4072_ = v___y_4108_;
                                    v___y_4073_ = v___y_4110_;
                                    v___y_4074_ = v___y_4111_;
                                    v___y_4075_ = v___y_4112_;
                                    v___y_4076_ = v___y_4113_;
                                    v___y_4077_ = v___y_4114_;
                                    v___y_4078_ = v___y_4115_;
                                    v___y_4079_ = v___y_4116_;
                                    v___y_4080_ = v___y_4117_;
                                    v___y_4081_ = v___y_4118_;
                                    v___y_4082_ = v___y_4119_;
                                    v___y_4083_ = v___y_4120_;
                                    state = 41;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_mvarIds_4125_);
                                v___y_4071_ = v___y_4107_;
                                v___y_4072_ = v___y_4108_;
                                v___y_4073_ = v___y_4110_;
                                v___y_4074_ = v___y_4111_;
                                v___y_4075_ = v___y_4112_;
                                v___y_4076_ = v___y_4113_;
                                v___y_4077_ = v___y_4114_;
                                v___y_4078_ = v___y_4115_;
                                v___y_4079_ = v___y_4116_;
                                v___y_4080_ = v___y_4117_;
                                v___y_4081_ = v___y_4118_;
                                v___y_4082_ = v___y_4119_;
                                v___y_4083_ = v___y_4120_;
                                state = 41;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4124_);
                            v___y_4071_ = v___y_4107_;
                            v___y_4072_ = v___y_4108_;
                            v___y_4073_ = v___y_4110_;
                            v___y_4074_ = v___y_4111_;
                            v___y_4075_ = v___y_4112_;
                            v___y_4076_ = v___y_4113_;
                            v___y_4077_ = v___y_4114_;
                            v___y_4078_ = v___y_4115_;
                            v___y_4079_ = v___y_4116_;
                            v___y_4080_ = v___y_4117_;
                            v___y_4081_ = v___y_4118_;
                            v___y_4082_ = v___y_4119_;
                            v___y_4083_ = v___y_4120_;
                            state = 41;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_4108_);
                        crate::leanh::lean_dec(v___y_4107_);
                        crate::leanh::lean_dec(v_goal_3715_);
                        v_a_4139_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                        v_isSharedCheck_4146_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4123_)) as u8;
                        if v_isSharedCheck_4146_ == 0 {
                            v___x_4141_ = v___x_4123_;
                            v_isShared_4142_ = v_isSharedCheck_4146_;
                            state = 49;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4139_);
                            crate::leanh::lean_dec(v___x_4123_);
                            v___x_4141_ = crate::leanh::lean_box(0);
                            v_isShared_4142_ = v_isSharedCheck_4146_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            47 => {
                if v_isShared_4134_ == 0 {
                    v___x_4136_ = v___x_4133_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
                    v___x_4136_ = v_reuseFailAlloc_4137_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4136_;
            }
            49 => {
                if v_isShared_4142_ == 0 {
                    v___x_4144_ = v___x_4141_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_4145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
                    v___x_4144_ = v_reuseFailAlloc_4145_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_4144_;
            }
            51 => {
                if crate::leanh::lean_obj_tag(v___y_4148_) == 0 {
                    crate::leanh::lean_dec(v___y_4149_);
                    v___y_3886_ = v_goal_3715_;
                    v_progress_3887_ = v_progress_3837_;
                    v___y_3888_ = v___y_3716_;
                    v___y_3889_ = v___y_3717_;
                    v___y_3890_ = v___y_3718_;
                    v___y_3891_ = v___y_3719_;
                    v___y_3892_ = v___y_3720_;
                    v___y_3893_ = v___y_3721_;
                    v___y_3894_ = v___y_3722_;
                    v___y_3895_ = v___y_3723_;
                    v___y_3896_ = v___y_3724_;
                    v___y_3897_ = v___y_3725_;
                    v___y_3898_ = v___y_3726_;
                    state = 19;
                    continue;
                } else {
                    v_val_4150_ = crate::leanh::lean_ctor_get(v___y_4148_, 0);
                    v___x_4151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__21);
                    v___x_4152_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___closed__22;
                    crate::leanh::lean_inc(v_val_4150_);
                    v___x_4153_ = l_Lean_Meta_Sym_isDefEqS(
                        v_val_4150_,
                        v___x_4151_,
                        v_progress_3836_,
                        v_progress_3836_,
                        v___x_4152_,
                        v___x_4152_,
                        v___y_3721_,
                        v___y_3722_,
                        v___y_3723_,
                        v___y_3724_,
                        v___y_3725_,
                        v___y_3726_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4153_) == 0 {
                        v_a_4154_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                        crate::leanh::lean_inc(v_a_4154_);
                        crate::leanh::lean_dec_ref_known(v___x_4153_, 1);
                        v___x_4155_ = (crate::leanh::lean_unbox(v_a_4154_) as u8);
                        crate::leanh::lean_dec(v_a_4154_);
                        if v___x_4155_ == 0 {
                            v___y_4107_ = v___y_4148_;
                            v___y_4108_ = v___y_4149_;
                            v_pureHNonTrue_4109_ = v_progress_3836_;
                            v___y_4110_ = v___y_3716_;
                            v___y_4111_ = v___y_3717_;
                            v___y_4112_ = v___y_3718_;
                            v___y_4113_ = v___y_3719_;
                            v___y_4114_ = v___y_3720_;
                            v___y_4115_ = v___y_3721_;
                            v___y_4116_ = v___y_3722_;
                            v___y_4117_ = v___y_3723_;
                            v___y_4118_ = v___y_3724_;
                            v___y_4119_ = v___y_3725_;
                            v___y_4120_ = v___y_3726_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___y_4148_, 1);
                            v___y_4010_ = v___y_4149_;
                            v_progress_4011_ = v_progress_3837_;
                            v_goal_4012_ = v_goal_3715_;
                            v___y_4013_ = v___y_3716_;
                            v___y_4014_ = v___y_3717_;
                            v___y_4015_ = v___y_3718_;
                            v___y_4016_ = v___y_3719_;
                            v___y_4017_ = v___y_3720_;
                            v___y_4018_ = v___y_3721_;
                            v___y_4019_ = v___y_3722_;
                            v___y_4020_ = v___y_3723_;
                            v___y_4021_ = v___y_3724_;
                            v___y_4022_ = v___y_3725_;
                            v___y_4023_ = v___y_3726_;
                            state = 33;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_4153_) == 0 {
                            v_a_4156_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                            crate::leanh::lean_inc(v_a_4156_);
                            crate::leanh::lean_dec_ref_known(v___x_4153_, 1);
                            v___x_4157_ = (crate::leanh::lean_unbox(v_a_4156_) as u8);
                            crate::leanh::lean_dec(v_a_4156_);
                            v___y_4107_ = v___y_4148_;
                            v___y_4108_ = v___y_4149_;
                            v_pureHNonTrue_4109_ = v___x_4157_;
                            v___y_4110_ = v___y_3716_;
                            v___y_4111_ = v___y_3717_;
                            v___y_4112_ = v___y_3718_;
                            v___y_4113_ = v___y_3719_;
                            v___y_4114_ = v___y_3720_;
                            v___y_4115_ = v___y_3721_;
                            v___y_4116_ = v___y_3722_;
                            v___y_4117_ = v___y_3723_;
                            v___y_4118_ = v___y_3724_;
                            v___y_4119_ = v___y_3725_;
                            v___y_4120_ = v___y_3726_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___y_4148_, 1);
                            crate::leanh::lean_dec(v___y_4149_);
                            crate::leanh::lean_dec(v_goal_3715_);
                            v_a_4158_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                            v_isSharedCheck_4165_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4153_)) as u8;
                            if v_isSharedCheck_4165_ == 0 {
                                v___x_4160_ = v___x_4153_;
                                v_isShared_4161_ = v_isSharedCheck_4165_;
                                state = 52;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4158_);
                                crate::leanh::lean_dec(v___x_4153_);
                                v___x_4160_ = crate::leanh::lean_box(0);
                                v_isShared_4161_ = v_isSharedCheck_4165_;
                                state = 52;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                if v_isShared_4161_ == 0 {
                    v___x_4163_ = v___x_4160_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
                    v___x_4163_ = v_reuseFailAlloc_4164_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4163_;
            }
            54 => {
                v___x_4168_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4169_ = l_Lean_Expr_isAppOfArity(v_arg_3828_, v___x_3884_, v___x_4168_);
                if v___x_4169_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_3828_);
                    v___x_4170_ = crate::leanh::lean_box(0);
                    v___y_4148_ = v___y_4167_;
                    v___y_4149_ = v___x_4170_;
                    state = 51;
                    continue;
                } else {
                    v___x_4171_ = l_Lean_Expr_appArg_x21(v_arg_3828_);
                    crate::leanh::lean_dec_ref(v_arg_3828_);
                    v___x_4172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4172_, 0, v___x_4171_);
                    v___y_4148_ = v___y_4167_;
                    v___y_4149_ = v___x_4172_;
                    state = 51;
                    continue;
                }
            }
            55 => {
                if v_isShared_4182_ == 0 {
                    v___x_4184_ = v___x_4181_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
                    v___x_4184_ = v_reuseFailAlloc_4185_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_4184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___boxed(
    mut v_goal_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4200_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0(
        v_goal_4187_,
        v___y_4188_,
        v___y_4189_,
        v___y_4190_,
        v___y_4191_,
        v___y_4192_,
        v___y_4193_,
        v___y_4194_,
        v___y_4195_,
        v___y_4196_,
        v___y_4197_,
        v___y_4198_,
    );
    crate::leanh::lean_dec(v___y_4198_);
    crate::leanh::lean_dec_ref(v___y_4197_);
    crate::leanh::lean_dec(v___y_4196_);
    crate::leanh::lean_dec_ref(v___y_4195_);
    crate::leanh::lean_dec(v___y_4194_);
    crate::leanh::lean_dec_ref(v___y_4193_);
    crate::leanh::lean_dec(v___y_4192_);
    crate::leanh::lean_dec_ref(v___y_4191_);
    crate::leanh::lean_dec(v___y_4190_);
    crate::leanh::lean_dec(v___y_4189_);
    crate::leanh::lean_dec_ref(v___y_4188_);
    return v_res_4200_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(
    mut v_goal_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
    mut v_a_4205_: *mut crate::leanh::LeanObject,
    mut v_a_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_goal_4201_);
    v___f_4214_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4214_, 0, v_goal_4201_);
    v___x_4215_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_tripleOfWP_spec__2___redArg(v_goal_4201_, v___f_4214_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
    return v___x_4215_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails___boxed(
    mut v_goal_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
    mut v_a_4223_: *mut crate::leanh::LeanObject,
    mut v_a_4224_: *mut crate::leanh::LeanObject,
    mut v_a_4225_: *mut crate::leanh::LeanObject,
    mut v_a_4226_: *mut crate::leanh::LeanObject,
    mut v_a_4227_: *mut crate::leanh::LeanObject,
    mut v_a_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails(
        v_goal_4216_,
        v_a_4217_,
        v_a_4218_,
        v_a_4219_,
        v_a_4220_,
        v_a_4221_,
        v_a_4222_,
        v_a_4223_,
        v_a_4224_,
        v_a_4225_,
        v_a_4226_,
        v_a_4227_,
    );
    crate::leanh::lean_dec(v_a_4227_);
    crate::leanh::lean_dec_ref(v_a_4226_);
    crate::leanh::lean_dec(v_a_4225_);
    crate::leanh::lean_dec_ref(v_a_4224_);
    crate::leanh::lean_dec(v_a_4223_);
    crate::leanh::lean_dec_ref(v_a_4222_);
    crate::leanh::lean_dec(v_a_4221_);
    crate::leanh::lean_dec_ref(v_a_4220_);
    crate::leanh::lean_dec(v_a_4219_);
    crate::leanh::lean_dec(v_a_4218_);
    crate::leanh::lean_dec_ref(v_a_4217_);
    return v_res_4229_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0(
    mut v_progress_4230_: u8,
    mut v_inst_4231_: *mut crate::leanh::LeanObject,
    mut v_a_4232_: *mut crate::leanh::LeanObject,
    mut v___y_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
    mut v___y_4241_: *mut crate::leanh::LeanObject,
    mut v___y_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4245_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___redArg(v_progress_4230_, v_a_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
    return v___x_4245_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0___boxed(
    mut v_progress_4246_: *mut crate::leanh::LeanObject,
    mut v_inst_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v___y_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
    mut v___y_4260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_progress_boxed_4261_: u8 = 0;
    let mut v_res_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_progress_boxed_4261_ = (crate::leanh::lean_unbox(v_progress_4246_) as u8);
    v_res_4262_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_solveSPredEntails_spec__0(v_progress_boxed_4261_, v_inst_4247_, v_a_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
    crate::leanh::lean_dec(v___y_4259_);
    crate::leanh::lean_dec_ref(v___y_4258_);
    crate::leanh::lean_dec(v___y_4257_);
    crate::leanh::lean_dec_ref(v___y_4256_);
    crate::leanh::lean_dec(v___y_4255_);
    crate::leanh::lean_dec_ref(v___y_4254_);
    crate::leanh::lean_dec(v___y_4253_);
    crate::leanh::lean_dec_ref(v___y_4252_);
    crate::leanh::lean_dec(v___y_4251_);
    crate::leanh::lean_dec(v___y_4250_);
    crate::leanh::lean_dec_ref(v___y_4249_);
    return v_res_4262_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
}
